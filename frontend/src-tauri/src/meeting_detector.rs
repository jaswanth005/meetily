// Auto-detect meetings and toggle recording without user input (macOS).
//
// Signals watched:
//   1. Call-only apps running — Webex, GoToMeeting, BlueJeans, Google Meet app
//   2. Zoom running AND a window title contains "Meeting" (skips the idle home screen)
//   3. A meeting URL open in a browser tab (Google Meet, Zoom web, Teams web,
//      Whereby, Gather, Around), read from each running browser via AppleScript.
//      Firefox has no AppleScript surface for its tabs, so it is not covered.
//
// Discord, Slack, Teams desktop and FaceTime are deliberately not watched by
// process: they idle in the background and would start recordings by mistake.
//
// State machine (see `Watcher`):
//   - A recording is started only when a meeting *starts*. If the user stops
//     it by hand, or the start fails, it is not retried until the next meeting.
//   - A meeting only counts as over after several quiet checks in a row.
//   - Only a recording the detector started is ever stopped by it; a
//     recording the user started by hand is never touched.
//   - The "Start recording when a meeting starts" setting turns it all off.
//
// Polling interval: 10s (light on CPU, catches meeting starts within 10s).

use std::collections::HashSet;
use std::process::Command;
use std::time::Duration;

use sysinfo::{ProcessRefreshKind, ProcessesToUpdate, System};
use tauri::{AppHandle, Runtime};

use crate::tray;

const POLL_INTERVAL: Duration = Duration::from_secs(10);

/// Checks to wait for a recording the detector asked for to begin (it may
/// need to load a model) before giving up on it.
const START_WAIT_CHECKS: u8 = 6;

/// Apps whose presence in the process list is a "call-only" signal — these
/// apps are launched to make/join a call, not left idling. Zoom is EXCLUDED
/// from this list even though it's the most common — Zoom often idles with
/// its home screen open, so we check its window title instead (see below).
const CALL_ONLY_PROCESSES: &[&str] = &[
    "Webex",       // Webex
    "GoToMeeting", // GoTo Meeting
    "BlueJeans",   // BlueJeans
    "GoogleMeet",  // Google Meet standalone app (if installed)
];

const ZOOM_PROCESS: &str = "zoom.us";

/// Browsers we can query for open tabs via AppleScript. Each name is both the
/// app's AppleScript name and its process name.
const BROWSERS: &[&str] = &[
    "Google Chrome",
    "Google Chrome Canary",
    "Brave Browser",
    "Microsoft Edge",
    "Safari",
    "Arc",
    "Wavebox",
    "Vivaldi",
    "Orion",
    "SigmaOS",
];

struct MeetingSite {
    name: &'static str,
    /// Matches this host and its subdomains (Zoom links use hosts like us02web.zoom.us).
    host: &'static str,
    path_prefix: &'static str,
    /// Accepts the path segment after `path_prefix` (the meeting or room id).
    is_meeting_id: fn(&str) -> bool,
}

/// Browser URLs that mean a meeting is in progress. Each needs a meeting id
/// after the prefix, so a site's home page does not count.
const MEETING_SITES: &[MeetingSite] = &[
    MeetingSite {
        name: "Google Meet",
        host: "meet.google.com",
        path_prefix: "/",
        is_meeting_id: is_meet_code,
    },
    MeetingSite {
        name: "Zoom",
        host: "zoom.us",
        path_prefix: "/j/",
        is_meeting_id: is_non_empty,
    },
    MeetingSite {
        name: "Zoom",
        host: "zoom.us",
        path_prefix: "/wc/",
        is_meeting_id: is_non_empty,
    },
    MeetingSite {
        name: "Microsoft Teams",
        host: "teams.microsoft.com",
        path_prefix: "/l/meetup-join/",
        is_meeting_id: is_non_empty,
    },
    MeetingSite {
        name: "Microsoft Teams",
        host: "teams.live.com",
        path_prefix: "/meet/",
        is_meeting_id: is_non_empty,
    },
    MeetingSite {
        name: "Whereby",
        host: "whereby.com",
        path_prefix: "/",
        is_meeting_id: is_whereby_room,
    },
    MeetingSite {
        name: "Gather",
        host: "app.gather.town",
        path_prefix: "/app/",
        is_meeting_id: is_non_empty,
    },
    MeetingSite {
        name: "Around",
        host: "around.co",
        path_prefix: "/r/",
        is_meeting_id: is_non_empty,
    },
];

fn is_non_empty(segment: &str) -> bool {
    !segment.is_empty()
}

const WHEREBY_NON_ROOM_SEGMENTS: &[&str] = &[
    "information",
    "pricing",
    "user",
    "login",
    "signin",
    "sign-in",
    "signup",
    "sign-up",
    "blog",
    "org",
    "embed",
    "product",
    "products",
    "solutions",
    "about",
    "download",
    "help",
    "support",
    "careers",
    "legal",
    "privacy",
    "terms",
];

fn is_whereby_room(segment: &str) -> bool {
    !segment.is_empty()
        && !WHEREBY_NON_ROOM_SEGMENTS.contains(&segment.to_ascii_lowercase().as_str())
}

/// Google Meet codes look like `abc-defg-hij`.
fn is_meet_code(segment: &str) -> bool {
    let parts: Vec<&str> = segment.split('-').collect();
    parts.len() == 3
        && parts
            .iter()
            .zip([3, 4, 3])
            .all(|(part, len)| part.len() == len && part.chars().all(|c| c.is_ascii_lowercase()))
}

/// Names the meeting site a browser tab URL belongs to, if it is a meeting.
fn meeting_site(url: &str) -> Option<&'static str> {
    let url = url::Url::parse(url).ok()?;
    let host = url.host_str()?;
    MEETING_SITES.iter().find_map(|site| {
        let host_matches = host == site.host
            || host
                .strip_suffix(site.host)
                .is_some_and(|sub| sub.ends_with('.'));
        let id = url
            .path()
            .strip_prefix(site.path_prefix)?
            .split('/')
            .next()?;
        (host_matches && (site.is_meeting_id)(id)).then_some(site.name)
    })
}

#[derive(Debug, PartialEq, Eq)]
enum Action {
    Start,
    Stop,
}

/// The recording the detector started, if any.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
enum Ours {
    #[default]
    None,
    /// Asked for; waiting for it to begin.
    Starting {
        checks_left: u8,
    },
    Recording,
}

/// Consecutive checks without a meeting before it counts as over, so one
/// failed or timed-out probe does not end a recording.
const END_AFTER_QUIET_CHECKS: u8 = 3;

#[derive(Debug, Default)]
struct Watcher {
    meeting_was_active: bool,
    quiet_checks: u8,
    ours: Ours,
}

impl Watcher {
    /// Decides what to do after one check.
    fn step(&mut self, meeting_active: bool, recording: bool) -> Option<Action> {
        self.quiet_checks = if meeting_active {
            0
        } else {
            self.quiet_checks.saturating_add(1)
        };
        let meeting_active = meeting_active
            || (self.meeting_was_active && self.quiet_checks < END_AFTER_QUIET_CHECKS);
        let meeting_started = meeting_active && !self.meeting_was_active;
        self.meeting_was_active = meeting_active;

        if let Ours::Starting { checks_left } = self.ours {
            self.ours = match (recording, checks_left) {
                (true, _) => Ours::Recording,
                (false, 0) => Ours::None,
                (false, n) => Ours::Starting { checks_left: n - 1 },
            };
        }

        match self.ours {
            Ours::None if meeting_started && !recording => {
                self.ours = Ours::Starting {
                    checks_left: START_WAIT_CHECKS,
                };
                Some(Action::Start)
            }
            // Stopped by hand (or failed): forget it, and don't restart this meeting.
            Ours::Recording if !recording => {
                self.ours = Ours::None;
                None
            }
            Ours::Recording if !meeting_active => {
                self.ours = Ours::None;
                Some(Action::Stop)
            }
            _ => None,
        }
    }
}

/// Reads what is running and which tabs are open.
struct Probe {
    system: System,
    /// Browsers we already warned about, so a refused permission logs once.
    warned: HashSet<&'static str>,
}

impl Probe {
    /// Names the meeting in progress, if any.
    fn find_meeting(&mut self) -> Option<String> {
        self.system.refresh_processes_specifics(
            ProcessesToUpdate::All,
            true,
            ProcessRefreshKind::new(),
        );
        let running: HashSet<String> = self
            .system
            .processes()
            .values()
            .map(|p| p.name().to_string_lossy().into_owned())
            .collect();

        if let Some(app) = CALL_ONLY_PROCESSES
            .iter()
            .find(|app| running.contains(**app))
        {
            return Some(app.to_string());
        }
        if running.contains(ZOOM_PROCESS) && zoom_window_indicates_meeting() {
            return Some("Zoom (in meeting)".into());
        }
        for browser in BROWSERS.iter().filter(|b| running.contains(**b)) {
            if let Some(site) = self.tab_urls(browser).iter().find_map(|u| meeting_site(u)) {
                return Some(format!("{} in {}", site, browser));
            }
        }
        None
    }

    fn tab_urls(&mut self, browser: &'static str) -> Vec<String> {
        let script = format!(
            r#"set urlList to {{}}
with timeout of 5 seconds
    tell application "{browser}"
        repeat with w in windows
            repeat with t in tabs of w
                try
                    set end of urlList to (URL of t as text)
                end try
            end repeat
        end repeat
    end tell
end timeout
set AppleScript's text item delimiters to linefeed
return urlList as text"#
        );
        let output = match Command::new("osascript").arg("-e").arg(&script).output() {
            Ok(output) => output,
            Err(e) => {
                self.warn_once(browser, || {
                    format!("[auto-detect] could not run osascript: {}", e)
                });
                return Vec::new();
            }
        };
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            // -1743: the user denied (or has not yet allowed) Automation access.
            if stderr.contains("-1743") {
                self.warn_once(browser, || format!(
                    "[auto-detect] not allowed to read {} tabs; allow Meetily under System Settings → Privacy & Security → Automation",
                    browser
                ));
            } else {
                self.warn_once(browser, || {
                    format!(
                        "[auto-detect] could not read {} tabs: {}",
                        browser,
                        stderr.trim()
                    )
                });
            }
            return Vec::new();
        }
        // Reading works (again), so a later failure is worth one more warning.
        self.warned.remove(browser);
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(str::to_string)
            .collect()
    }

    fn warn_once(&mut self, browser: &'static str, message: impl FnOnce() -> String) {
        if self.warned.insert(browser) {
            log::warn!("{}", message());
        }
    }
}

/// Ask System Events for Zoom's window titles and check if one contains "Meeting"
/// (idle Zoom shows "Zoom" or "Zoom - Free Account", an active call "Zoom Meeting").
fn zoom_window_indicates_meeting() -> bool {
    let script = r#"
    with timeout of 5 seconds
        tell application "System Events"
            try
                tell process "zoom.us"
                    set winTitles to name of every window
                    repeat with t in winTitles
                        if t contains "Meeting" then return "yes"
                    end repeat
                end tell
            end try
            return "no"
        end tell
    end timeout
    "#;
    match Command::new("osascript").arg("-e").arg(script).output() {
        Ok(o) if o.status.success() => String::from_utf8_lossy(&o.stdout).trim() == "yes",
        _ => false,
    }
}

/// Spawn the background watcher. Runs for the lifetime of the app on its own
/// thread, because each check waits on osascript.
pub fn spawn<R: Runtime>(app: AppHandle<R>) {
    let spawned = std::thread::Builder::new()
        .name("meeting-detector".into())
        .spawn(move || {
            log::info!(
                "[auto-detect] meeting watcher started (interval={}s)",
                POLL_INTERVAL.as_secs()
            );
            let mut watcher = Watcher::default();
            let mut probe = Probe {
                system: System::new(),
                warned: HashSet::new(),
            };

            loop {
                std::thread::sleep(POLL_INTERVAL);

                if !crate::audio::recording_preferences::auto_detect_meetings(&app) {
                    watcher = Watcher::default();
                    continue;
                }

                let meeting = probe.find_meeting();
                let recording = tauri::async_runtime::block_on(
                    crate::audio::recording_commands::is_recording(),
                );

                match watcher.step(meeting.is_some(), recording) {
                    Some(Action::Start) => {
                        log::info!(
                            "[auto-detect] meeting detected ({}) → auto-starting recording",
                            meeting.as_deref().unwrap_or_default()
                        );
                        tray::toggle_recording_handler(&app);
                    }
                    Some(Action::Stop) => {
                        log::info!("[auto-detect] no meeting active → stopping our auto-recording");
                        tray::toggle_recording_handler(&app);
                    }
                    None => {}
                }
            }
        });
    if let Err(e) = spawned {
        log::error!("[auto-detect] failed to start meeting watcher: {}", e);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn meeting_urls_are_recognised() {
        let meetings = [
            ("https://meet.google.com/abc-defg-hij", "Google Meet"),
            (
                "https://meet.google.com/abc-defg-hij?authuser=1",
                "Google Meet",
            ),
            ("https://zoom.us/j/1234567890?pwd=x", "Zoom"),
            ("https://us02web.zoom.us/j/1234567890", "Zoom"),
            ("https://app.zoom.us/wc/1234567890/join", "Zoom"),
            (
                "https://teams.microsoft.com/l/meetup-join/19%3ameeting_x/0",
                "Microsoft Teams",
            ),
            ("https://teams.live.com/meet/9876543210", "Microsoft Teams"),
            ("https://whereby.com/my-room", "Whereby"),
            ("https://app.gather.town/app/abc/office", "Gather"),
            ("https://around.co/r/standup", "Around"),
        ];
        for (url, site) in meetings {
            assert_eq!(meeting_site(url), Some(site), "{url}");
        }
    }

    #[test]
    fn pages_that_are_not_meetings_are_ignored() {
        for url in [
            "https://meet.google.com/",
            "https://meet.google.com/landing",
            "https://zoom.us/",
            "https://zoom.us/signin",
            "https://teams.microsoft.com/v2/",
            "https://whereby.com/",
            "https://whereby.com/pricing",
            "https://whereby.com/information",
            "https://notzoom.us/j/123",
            "https://www.google.com/search?q=meet.google.com/abc-defg-hij",
            "missing value",
            "",
        ] {
            assert_eq!(meeting_site(url), None, "{url}");
        }
    }

    /// Feeds (meeting_active, recording) checks and returns the actions taken.
    fn run(checks: &[(bool, bool)]) -> Vec<Option<Action>> {
        let mut watcher = Watcher::default();
        checks.iter().map(|&(m, r)| watcher.step(m, r)).collect()
    }

    #[test]
    fn starts_when_a_meeting_starts_and_stops_when_it_ends() {
        assert_eq!(
            run(&[
                (false, false),
                (true, false),
                (true, true),
                (true, true),
                (false, true),
                (false, true),
                (false, true)
            ]),
            [
                None,
                Some(Action::Start),
                None,
                None,
                None,
                None,
                Some(Action::Stop)
            ]
        );
    }

    #[test]
    fn a_single_missed_check_neither_stops_nor_restarts() {
        assert_eq!(
            run(&[
                (true, false),
                (true, true),
                (false, true),
                (true, true),
                (false, true),
                (false, true),
                (true, true)
            ]),
            [Some(Action::Start), None, None, None, None, None, None]
        );
    }

    #[test]
    fn never_stops_a_recording_the_user_started() {
        assert_eq!(
            run(&[(false, true), (true, true), (false, true), (false, true)]),
            [None, None, None, None]
        );
    }

    #[test]
    fn does_not_restart_after_the_user_stops_it_during_the_meeting() {
        assert_eq!(
            run(&[
                (true, false),
                (true, true),
                (true, false),
                (true, false),
                (false, false)
            ]),
            [Some(Action::Start), None, None, None, None]
        );
    }

    #[test]
    fn waits_for_a_slow_start_then_stops_it_when_the_meeting_ends() {
        assert_eq!(
            run(&[
                (true, false),
                (true, false),
                (true, false),
                (true, true),
                (false, true),
                (false, true),
                (false, true)
            ]),
            [
                Some(Action::Start),
                None,
                None,
                None,
                None,
                None,
                Some(Action::Stop)
            ]
        );
    }

    #[test]
    fn gives_up_on_a_start_that_never_happens_without_retrying() {
        let mut checks = vec![(true, false); 2 + START_WAIT_CHECKS as usize];
        checks.push((true, true)); // the user starts one by hand later
        checks.push((false, true));
        let actions = run(&checks);
        assert_eq!(actions[0], Some(Action::Start));
        assert!(actions[1..].iter().all(Option::is_none), "{actions:?}");
    }

    #[test]
    fn starts_again_for_the_next_meeting() {
        assert_eq!(
            run(&[
                (true, false),
                (true, true),
                (false, true),
                (false, true),
                (false, true),
                (false, false),
                (true, false)
            ]),
            [
                Some(Action::Start),
                None,
                None,
                None,
                Some(Action::Stop),
                None,
                Some(Action::Start)
            ]
        );
    }
}

use std::fs;
use std::process::Command;
use zed::settings::LspSettings;
use zed::LanguageServerId;
use zed_extension_api::{self as zed, Result};

struct KokaExtension {
    cached_binary_path: Result<String>,
}

impl KokaExtension {
    fn language_server_binary_path(
        &mut self,
        language_server_id: &LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<String> {
        if let Some(path) = LspSettings::for_worktree("koka", worktree)
            .ok()
            .and_then(|settings| {
                settings.initialization_options.and_then(|options| {
                    options
                        .get("devPath")
                        .and_then(|path| path.as_str().map(|p| p.to_string()))
                })
            })
        {
            if fs::metadata(path.clone()).map_or(false, |stat| stat.is_file()) {
                return Ok(path);
            }
            return Err("Dev path invalid".to_string());
        }

        if let Ok(path) = &self.cached_binary_path {
            if fs::metadata(path).map_or(false, |stat| stat.is_file()) {
                return Ok(path.clone());
            }
        }

        worktree.which("koka").ok_or("Koka not found".to_string())
    }
}

impl zed::Extension for KokaExtension {
    fn new() -> Self {
        Self {
            cached_binary_path: Err("No search performed yet".to_string()),
        }
    }

    fn language_server_command(
        &mut self,
        language_server_id: &LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        self.cached_binary_path = self.language_server_binary_path(language_server_id, worktree);
        self.cached_binary_path.clone().and_then(|koka_bin| {
            return Ok(zed::Command {
                command: koka_bin.to_string(),
                args: vec![
                    "--language-server".to_string(),
                    "--buildtag=zed".to_string(),
                    "--lsstdio".to_string(),
                ],
                env: Default::default(),
            });
        })
    }
}

zed::register_extension!(KokaExtension);

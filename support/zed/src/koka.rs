use zed::LanguageServerId;
use zed_extension_api::{self as zed, Result};

struct KokaExtension;

impl zed::Extension for KokaExtension {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        _language_server_id: &LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        let Some(koka_bin) = worktree.which("koka") else {
            return Err("koka not found".to_string());
        };
        Ok(zed::Command {
            command: koka_bin.to_string(),
            args: vec![
                "--language-server".to_string(),
                "--buildtag=zed".to_string(),
                "--lsstdio".to_string(),
            ],
            env: Default::default(),
        })
    }
}

zed::register_extension!(KokaExtension);

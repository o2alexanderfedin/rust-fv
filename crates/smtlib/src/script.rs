use crate::command::Command;

/// An SMT-LIB script: a sequence of commands.
#[derive(Debug, Clone, Default)]
pub struct Script {
    commands: Vec<Command>,
}

impl Script {
    pub fn new() -> Self {
        Self {
            commands: Vec::new(),
        }
    }

    pub fn with_commands(commands: Vec<Command>) -> Self {
        Self { commands }
    }

    pub fn push(&mut self, cmd: Command) {
        self.commands.push(cmd);
    }

    pub fn extend(&mut self, cmds: impl IntoIterator<Item = Command>) {
        self.commands.extend(cmds);
    }

    pub fn commands(&self) -> &[Command] {
        &self.commands
    }

    pub fn into_commands(self) -> Vec<Command> {
        self.commands
    }

    pub fn len(&self) -> usize {
        self.commands.len()
    }

    pub fn is_empty(&self) -> bool {
        self.commands.is_empty()
    }
}

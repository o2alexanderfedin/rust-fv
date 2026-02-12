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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sort::Sort;
    use crate::term::Term;

    #[test]
    fn new_creates_empty_script() {
        let script = Script::new();
        assert!(script.is_empty());
        assert_eq!(script.len(), 0);
        assert!(script.commands().is_empty());
    }

    #[test]
    fn default_creates_empty_script() {
        let script = Script::default();
        assert!(script.is_empty());
        assert_eq!(script.len(), 0);
    }

    #[test]
    fn with_commands_creates_script() {
        let cmds = vec![
            Command::SetLogic("QF_LIA".to_string()),
            Command::DeclareConst("x".to_string(), Sort::Int),
            Command::CheckSat,
        ];
        let script = Script::with_commands(cmds);
        assert_eq!(script.len(), 3);
        assert!(!script.is_empty());
    }

    #[test]
    fn push_adds_command() {
        let mut script = Script::new();
        assert!(script.is_empty());
        script.push(Command::CheckSat);
        assert_eq!(script.len(), 1);
        assert!(!script.is_empty());
        script.push(Command::GetModel);
        assert_eq!(script.len(), 2);
    }

    #[test]
    fn extend_adds_multiple_commands() {
        let mut script = Script::new();
        script.extend(vec![
            Command::SetLogic("QF_BV".to_string()),
            Command::CheckSat,
            Command::Exit,
        ]);
        assert_eq!(script.len(), 3);
    }

    #[test]
    fn commands_returns_slice() {
        let mut script = Script::new();
        script.push(Command::CheckSat);
        script.push(Command::GetModel);
        let cmds = script.commands();
        assert_eq!(cmds.len(), 2);
        assert_eq!(cmds[0], Command::CheckSat);
        assert_eq!(cmds[1], Command::GetModel);
    }

    #[test]
    fn into_commands_returns_vec() {
        let mut script = Script::new();
        script.push(Command::CheckSat);
        script.push(Command::Exit);
        let cmds = script.into_commands();
        assert_eq!(cmds.len(), 2);
        assert_eq!(cmds[0], Command::CheckSat);
        assert_eq!(cmds[1], Command::Exit);
    }

    #[test]
    fn len_and_is_empty_consistent() {
        let script = Script::new();
        assert_eq!(script.len(), 0);
        assert!(script.is_empty());

        let script = Script::with_commands(vec![Command::CheckSat]);
        assert_eq!(script.len(), 1);
        assert!(!script.is_empty());
    }

    #[test]
    fn with_commands_empty_vec() {
        let script = Script::with_commands(vec![]);
        assert!(script.is_empty());
        assert_eq!(script.len(), 0);
    }

    #[test]
    fn push_preserves_order() {
        let mut script = Script::new();
        script.push(Command::SetLogic("QF_LIA".to_string()));
        script.push(Command::DeclareConst("x".to_string(), Sort::Int));
        script.push(Command::Assert(Term::IntGt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(0)),
        )));
        script.push(Command::CheckSat);

        let cmds = script.commands();
        assert!(matches!(&cmds[0], Command::SetLogic(l) if l == "QF_LIA"));
        assert!(matches!(&cmds[1], Command::DeclareConst(n, Sort::Int) if n == "x"));
        assert!(matches!(&cmds[2], Command::Assert(_)));
        assert!(matches!(&cmds[3], Command::CheckSat));
    }

    #[test]
    fn extend_after_push() {
        let mut script = Script::new();
        script.push(Command::SetLogic("QF_BV".to_string()));
        script.extend(vec![Command::CheckSat, Command::GetModel]);
        assert_eq!(script.len(), 3);
        assert!(matches!(&script.commands()[0], Command::SetLogic(_)));
        assert_eq!(script.commands()[1], Command::CheckSat);
        assert_eq!(script.commands()[2], Command::GetModel);
    }
}

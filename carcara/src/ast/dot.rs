use super::{Proof, ProofCommand, ProofStep, Rc, Subproof, Term};
use std::io;

struct DotWriter<'a, W: io::Write + ?Sized> {
    dest: &'a mut W,
    /// Maps (depth, index) to a global node index.
    node_indices: Vec<Vec<usize>>,
    next_index: usize,
    cluster_count: usize,
}

impl<'a, W: io::Write + ?Sized> DotWriter<'a, W> {
    fn new(dest: &'a mut W) -> Self {
        Self {
            dest,
            node_indices: vec![Vec::new()],
            next_index: 0,
            cluster_count: 0,
        }
    }

    fn alloc_index(&mut self) -> usize {
        let idx = self.next_index;
        self.node_indices.last_mut().unwrap().push(idx);
        self.next_index += 1;
        idx
    }

    fn resolve(&self, depth: usize, index: usize) -> usize {
        self.node_indices[depth][index]
    }

    fn write_commands(&mut self, commands: &[ProofCommand]) -> io::Result<()> {
        for command in commands {
            match command {
                ProofCommand::Assume { id, term } => {
                    let idx = self.alloc_index();
                    let conclusion = format_clause(std::slice::from_ref(term));
                    writeln!(
                        self.dest,
                        "\t{idx} [ label = \"{{{}|ASSUME}}\", comment = \"{{}}\" ];",
                        sanitize(&format!("{id}: {conclusion}")),
                    )?;
                }
                ProofCommand::Step(step) => {
                    self.write_step(step)?;
                }
                ProofCommand::Subproof(subproof) => {
                    self.write_subproof(subproof)?;
                }
            }
        }
        Ok(())
    }

    fn write_step(&mut self, step: &ProofStep) -> io::Result<()> {
        let idx = self.alloc_index();
        let conclusion = format_clause(&step.clause);
        let rule = &step.rule;
        let args = if step.args.is_empty() {
            String::new()
        } else {
            let args_str: Vec<_> = step.args.iter().map(|a| format!("{a}")).collect();
            format!(" :args [ {} ]", args_str.join(", "))
        };
        writeln!(
            self.dest,
            "\t{idx} [ label = \"{{{}|{}{}}}\", comment = \"{{}}\" ];",
            sanitize(&format!("{}: {conclusion}", step.id)),
            sanitize(rule),
            sanitize(&args),
        )?;
        for &premise in &step.premises {
            let src = self.resolve(premise.0, premise.1);
            writeln!(self.dest, "\t{src} -> {idx};")?;
        }
        for &discharge in &step.discharge {
            let src = self.resolve(discharge.0, discharge.1);
            writeln!(self.dest, "\t{src} -> {idx};")?;
        }
        Ok(())
    }

    fn write_subproof(&mut self, subproof: &Subproof) -> io::Result<()> {
        let cluster_id = self.cluster_count;
        self.cluster_count += 1;

        self.node_indices.push(Vec::new());

        writeln!(self.dest, "\tsubgraph cluster_{cluster_id} {{")?;
        writeln!(self.dest, "\t\tstyle=dashed;")?;

        // Temporarily swap dest to add extra indentation inside clusters.
        self.write_commands(&subproof.commands)?;

        writeln!(self.dest, "\t}}")?;

        // The subproof's end step is the last command. Record it at the parent depth so that
        // references from outside the subproof can resolve it.
        let last_idx = *self.node_indices.last().unwrap().last().unwrap();
        self.node_indices.pop();
        self.node_indices.last_mut().unwrap().push(last_idx);

        Ok(())
    }
}

/// Writes a DOT representation of the proof to `dest`, using the same format as cvc5's DOT proof
/// printer.
pub fn write_dot(proof: &Proof, dest: &mut dyn io::Write) -> io::Result<()> {
    writeln!(dest, "digraph proof {{")?;
    writeln!(dest, "\trankdir=\"BT\";")?;
    writeln!(dest, "\tnode [shape=record];")?;

    let mut writer = DotWriter::new(dest);
    writer.write_commands(&proof.commands)?;

    writeln!(writer.dest, "}}")?;
    Ok(())
}

fn format_clause(clause: &[Rc<Term>]) -> String {
    if clause.is_empty() {
        "(cl)".to_owned()
    } else if clause.len() == 1 {
        format!("{}", clause[0])
    } else {
        let terms: Vec<_> = clause.iter().map(|t| format!("{t}")).collect();
        format!("(cl {})", terms.join(" "))
    }
}

/// Escapes characters that are special in DOT record labels.
fn sanitize(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '>' => out.push_str("\\>"),
            '<' => out.push_str("\\<"),
            '{' => out.push_str("\\{"),
            '}' => out.push_str("\\}"),
            '|' => out.push_str("\\|"),
            _ => out.push(c),
        }
    }
    out
}

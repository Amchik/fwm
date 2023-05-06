use std::{fs, path::PathBuf, process::ExitCode, io::{self, Write}};

use clap::Parser;
use fwm_as::{lex::Lex, tree::SyntaxTree, writer};
use fwm_as_vmgen::{FWMInfo, VMInfoBuilder};
use fwm_base::{
    opcode::OPCodeKind,
    parser,
    runner::{FWMRunner, FWMSignal},
};

#[derive(Parser)]
#[command(version, about, long_about, arg_required_else_help(true))]
struct Args {
    /// File to execute
    file: PathBuf,

    /// Assembly file
    #[arg(short, long)]
    assembly: bool,

    /// Output file for bytecode (--assembly)
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Do not execute file
    #[arg(short, long)]
    no_exec: bool,

    /// Do not use VM built-in defs
    #[arg(long)]
    no_builtin: bool,
}

fn main() -> ExitCode {
    let Args {
        file,
        assembly,
        output,
        no_exec,
        no_builtin,
    } = Args::parse();

    let bytecode = if assembly {
        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Failed to read file to UTF-8: {e}");

                return ExitCode::FAILURE;
            }
        };
        let tokens: Vec<_> = match Lex::new(source.as_str()).collect() {
            Ok(v) => v,
            Err(e) => {
                let fragment = &source[e.start.max(10) - 10..e.end.min(source.len() - 10) + 10];
                eprintln!("error:{}:{}: {}\n{fragment}", e.start, e.end, e.kind);

                return ExitCode::FAILURE;
            }
        };
        let tree = match SyntaxTree::new(tokens.iter()) {
            Ok(v) => v.0,
            Err(e) => {
                let tokens = &tokens[e.idx.max(1) - 1..e.idx.min(tokens.len() - 6) + 6];
                eprintln!("error:@{}: {}\n{tokens:?}", e.idx, e.kind);

                return ExitCode::FAILURE;
            }
        };
        let builtin = if no_builtin {
            vec![]
        } else {
            VMInfoBuilder::from_vm_opcodes::<FWMInfo>().to_syntax_items()
        };
        let ctx = writer::Context::new()
            .populate(builtin.iter())
            .populate(tree.iter());
        match ctx.generate(tree.iter()) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("error:{}: {}", e.expr_id, e.kind);

                return ExitCode::FAILURE;
            }
        }
    } else {
        match fs::read(file) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("Failed to read file: {e}");

                return ExitCode::FAILURE;
            }
        }
    };

    if let Some(output) = output {
        if assembly {
            if let Err(e) = fs::write(output, &bytecode) {
                eprintln!("Failed to write to file: {e}");

                return ExitCode::FAILURE;
            }
        }
    }

    let opcodes = {
        let exprs: Result<Option<Vec<_>>, _> = parser::Parser::new(&bytecode)
            .into_iter()
            .map(|f| f.map(|r| OPCodeKind::from_raw(r.opcode).and_then(|o| o.to_opcode(&r.args))))
            .collect();

        match exprs {
            Ok(Some(v)) => v,
            Ok(None) => {
                eprintln!("vm-error: unknown opcode kind or syntax");
                return ExitCode::FAILURE;
            }
            Err(e) => {
                eprintln!("vm-error: {e}");
                return ExitCode::FAILURE;
            }
        }
    };

    if no_exec {
        return ExitCode::SUCCESS;
    }

    let mut fwm = FWMRunner::new(opcodes);

    loop {
        match fwm.run() {
            FWMSignal::Continue => continue,
            FWMSignal::EOF => break,
            FWMSignal::Signaled => {
                eprintln!("runtime-error: signaled");
                break;
            }
            FWMSignal::Data(what) => {
                _ = io::stdout().write(what);
            }
        }
    }

    ExitCode::SUCCESS
}

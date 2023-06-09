use std::io::{Cursor, Read, Write};

use sim86::{disassemble, execute_with_trace};

#[derive(clap::Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    action: Action,
}

#[derive(clap::Subcommand, Debug)]
enum Action {
    Disassemble,
    Exec,
}

fn main() {
    let args = <Args as clap::Parser>::parse();

    let mut stdin = std::io::stdin().lock();
    let mut stdout = std::io::BufWriter::new(std::io::stdout());

    match args.action {
        Action::Disassemble => {
            stdout.write_all(b"bits 16\n\n").unwrap();
            disassemble(stdin, &mut stdout);
            stdout.flush().unwrap();
        }
        Action::Exec => {
            let mut buffer: Vec<u8> = Vec::new();
            stdin.read_to_end(&mut buffer).unwrap();
            drop(stdin);
            let buffer: &[u8] = &buffer;
            let input: Cursor<&[u8]> = Cursor::new(buffer);

            writeln!(stdout, "trace:").unwrap();
            let final_machine_state = execute_with_trace(input, &mut stdout, true);
            writeln!(stdout).unwrap();
            writeln!(stdout, "final register state:").unwrap();
            final_machine_state
                .print_all_registers(&mut stdout)
                .unwrap();
            stdout.flush().unwrap();
        }
    }
}

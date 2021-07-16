mod commands;
use commands::*;

use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{self, BufRead};
use std::path::Path;
use std::process::{exit, Command, Stdio};

use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use tempfile::tempdir;
use walkdir::WalkDir;

// NOTE: For simplicity I assume that every outer command starts on a new line.

const BEGIN: &str = "DefineSnippet";
const END: &str = "EndSnippet";

const OPEN: &str = "\\<open>";
const CLOSE: &str = "\\<close>";

const ISA_NEWLINE: &str = "\\isanewline";

/*
 * Isabelle
 */

fn make_root(theory: &str, library: bool) -> String {
    format!(
        "session isasnips = {} +
  theories
    {}
  document_files
    \"root.tex\"",
        if library { "\"HOL-Library\"" } else { "HOL" },
        theory
    )
}

fn call_isabelle(path: &Path, cmds: &[&str]) -> io::Result<()> {
    println!("Running isabelle {} >>>", cmds.join(" "));

    let stdout = Command::new("isabelle")
        .current_dir(path)
        .stdout(Stdio::piped())
        .args(cmds)
        .spawn()
        .expect("Failed to call isabelle command")
        .stdout
        .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "Could not capture stdout."))?;

    let reader = io::BufReader::new(stdout);

    reader
        .lines()
        .filter_map(|line| line.ok())
        .for_each(|line| println!("  {}", line));

    println!("<<<");

    Ok(())
}

fn mkroot(isa_path: &Path, temp_dir: &Path, library: bool) -> io::Result<OsString> {
    let theory_stem = isa_path.file_stem().expect("No theory file.");

    let theory = theory_stem
        .to_str()
        .expect("Could not convert theory name to str");

    let new_theory = process_theory(isa_path)?;
    let new_path = temp_dir.join(Path::new(theory).with_extension("thy"));
    fs::write(new_path, new_theory)?;

    call_isabelle(temp_dir, &["mkroot", "-n", "isasnips"])?;

    let root_path = temp_dir.join(Path::new("ROOT"));
    let root = make_root(theory, library);
    fs::write(root_path, root)?;

    Ok(theory_stem.to_os_string())
}

/*
 * Generate Snippets
 */

fn escape_underscores(s: &str) -> String {
    s.replace("_", "-")
}

fn strip_superscripts(s: &str) -> String {
    s.replace("^", "")
}

fn snippet_name(key: &str, name: &str) -> String {
    format!(
        "{}:{}",
        strip_superscripts(&escape_underscores(key)),
        strip_superscripts(&escape_underscores(name))
    )
}

fn text_raw(s: &str) -> String {
    vec!["text_raw", " ", OPEN, s, CLOSE].join("")
}

fn begin_marker(name: &str) -> String {
    let cmd = vec![BEGIN, name].join(" ");
    text_raw(&cmd)
}

fn end_marker() -> String {
    text_raw(END)
}

fn make_words(s: &str) -> Vec<String> {
    let mut words: Vec<String> = vec![];
    let mut current_word = String::new();

    let mut pushing_symbol = false;
    let mut current_symbol = String::new();

    let mut inside_dquote = false;

    fn breaker(c: char) -> bool {
        vec!['[', ']', '(', ')', ':', '=', '\\'].contains(&c)
    }

    for c in s.chars() {
        if c == '"' {
            if inside_dquote {
                words.push(CLOSE.to_owned());
            } else {
                words.push(OPEN.to_owned());
            }

            inside_dquote = !inside_dquote;
            continue;
        }

        if pushing_symbol {
            if c == '>' {
                if current_symbol == "open" {
                    words.push(OPEN.to_owned());
                } else if current_symbol == "close" {
                    words.push(CLOSE.to_owned());
                } else {
                    current_word.push_str(&current_symbol);
                }

                current_symbol.clear();
                pushing_symbol = false;
            } else if c != '<' {
                current_symbol.push(c);
            }
            continue;
        }

        if c.is_whitespace() || breaker(c) {
            if !current_word.is_empty() {
                words.push(current_word.clone());
                current_word.clear();
            }
        }

        if breaker(c) {
            if c == '\\' {
                pushing_symbol = true;
            } else {
                words.push(c.to_string());
            }
        } else if !c.is_whitespace() {
            current_word.push(c);
        }
    }

    if pushing_symbol && !current_symbol.is_empty() {
        words.push(current_symbol);
    }

    if !current_word.is_empty() {
        words.push(current_word);
    }

    words
}

type Lines = Vec<String>;
type Chunk = (String, CmdType, Lines);

fn chunk_theory(thy: String) -> Vec<Chunk> {
    let mut chunks = vec![];

    let mut current_cmd: Option<(String, CmdType)> = None;
    let mut current_chunk: Vec<String> = vec![];

    for line in thy.lines() {
        let tokens = make_words(line);

        let mut first = tokens.first().map(|s| s.to_string());
        if let Some(c) = tokens.first() {
            if c == "(" && tokens.get(1).map_or(false, |c| c == "*") {
                first = Some("(*".to_string());
            }

            if c == "*" && tokens.get(1).map_or(false, |c| c == ")") {
                first = Some("*)".to_string());
            }
        }

        let cmd_type = first.clone().and_then(|f| get_cmd_type(&f));

        match cmd_type {
            Some(CmdType::Outer) | Some(CmdType::OuterNamed) => match current_cmd {
                None => {}
                Some((ref cmd, ref typ)) => {
                    chunks.push((cmd.to_owned(), typ.clone(), current_chunk.clone()));
                    current_chunk.clear();
                }
            },
            Some(CmdType::Inner) | None => {}
        }

        match cmd_type {
            Some(CmdType::Outer) | Some(CmdType::OuterNamed) => {
                current_cmd = first.map(|s| (s.clone(), cmd_type.unwrap()));
            }
            Some(CmdType::Inner) | None => {}
        }

        current_chunk.push(line.to_owned());
    }

    if !current_chunk.is_empty() {
        match current_cmd {
            Some((cmd, typ)) if !current_chunk.is_empty() => {
                chunks.push((cmd, typ, current_chunk.clone()));
            }
            _ => {}
        }
    }

    chunks
}

fn chunk_name(cmd: &str, words: &[String], last_fun: &Option<String>) -> Option<String> {
    let mut inside_parens = 0;
    let mut inside_open = 0;

    let mut name_parts = vec![];
    let mut content = vec![];

    // Names occur before these.
    let markers = vec![
        "[", ":", "=", "where", "and", "by", "imports", "begin", "fixes", "assumes", "shows",
    ];

    for i in 0..words.len() - 1 {
        if words[i] == "(" {
            inside_parens += 1;
        } else if words[i] == ")" {
            inside_parens -= 1;
        } else if inside_parens == 0 && words[i] == OPEN {
            inside_open += 1;
        } else if inside_parens == 0 && words[i] == CLOSE {
            inside_open -= 1;
        } else if inside_open > 0 {
            content.push(words[i].clone());
        }

        if words[i] == CLOSE && inside_open == 0 {
            break;
        }

        if inside_parens == 0
            && inside_open == 0
            && words[i] != ")"
            && !words[i].starts_with("'")
            && words[i] != CLOSE
        {
            name_parts.push(words[i].clone());
        }

        if inside_parens == 0 && inside_open == 0 && markers.contains(&words[i + 1].as_str()) {
            break;
        }
    }

    let mut name = None;

    if name_parts.len() > 1 {
        name = Some(
            name_parts[1..]
                .into_iter()
                .map(|s| s.to_string())
                .collect::<String>(),
        );
    }

    if name.is_none() && !content.is_empty() && (cmd == "definition" || cmd == "abbreviation") {
        // Make sure to include subscripts. A bit of a hack.
        let mut parts = vec![];
        parts.push(content[0].clone());
        let mut i = 1;
        while content[i].contains("^") {
            parts.push(content[i].clone());
            i += 1;
        }
        name = Some(parts.join(""));
    }

    if cmd == "termination" && name_parts.len() > 1 && name_parts[1] == "proof" {
        name = None;
    }

    if name.is_none() && last_fun.is_some() && (cmd == "termination") {
        name = last_fun.clone();
    }

    name.map(|n| snippet_name(cmd, &n))
}

fn process_theory(thy_path: &Path) -> io::Result<String> {
    let thy = fs::read_to_string(thy_path)?;

    let chunks = chunk_theory(thy);

    let mut annotated: Vec<String> = vec![];
    let mut last_fun = None;
    let mut hashes = HashMap::new();

    for chunk in &chunks {
        let (cmd, cmd_type, cont_lines) = chunk;
        let cont = cont_lines.join("\n");
        let words = make_words(&cont);

        if words.is_empty() {
            continue;
        }

        let mut outer_name = None;
        if *cmd_type == CmdType::OuterNamed {
            outer_name = chunk_name(cmd, &words, &last_fun);
        }

        let name = match outer_name {
            Some(n) => n,
            None => {
                let mut hasher = DefaultHasher::new();
                words.hash(&mut hasher);
                let hash = hasher.finish();
                let suffix = hashes.entry(hash).or_insert(0);
                let name = if *suffix > 0 {
                    snippet_name(cmd, &format!("{:x}-{}", hash, suffix))
                } else {
                    snippet_name(cmd, &format!("{:x}", hash))
                };
                *suffix += 1;
                name
            }
        };

        if cmd.starts_with("fun") {
            let colon = name.find(':').unwrap_or(0);
            let last_name = name[colon + 1..].to_string();
            last_fun = Some(last_name);
        }

        annotated.push(begin_marker(&name));
        annotated.extend(chunk.2.clone());
        if annotated.last().map_or(false, |l| l.is_empty()) {
            annotated.pop();
        }
        annotated.push(end_marker());
        annotated.push(String::new());
    }

    Ok(annotated.join("\n"))
}

fn has_ext(p: &Path, ext: &str) -> bool {
    p.extension().map_or(false, |e| e == ext)
}

fn copy_isabelle(
    isa_path: &Path,
    temp_path: &Path,
    user_theories: &[OsString],
) -> io::Result<Vec<OsString>> {
    let mut processed = vec![];

    for entry in WalkDir::new(isa_path) {
        let entry = entry.expect("Could not read file.");
        let typ = entry.file_type();

        let new_entry_path = entry
            .path()
            .strip_prefix(isa_path)
            .expect("Could not strip prefix.");

        let new_path = temp_path.join(new_entry_path);

        if typ.is_dir() {
            fs::create_dir_all(new_path)?;
        } else if has_ext(&entry.path(), "thy") {
            let theory = entry
                .path()
                .file_stem()
                .expect("Could not extract file stem.");

            if user_theories.is_empty() || user_theories.contains(&theory.to_os_string()) {
                let new_theory = process_theory(entry.path())?;
                fs::write(new_path, new_theory)?;
                processed.push(theory.to_os_string());
            } else {
                fs::copy(entry.path(), new_path)?;
            }
        } else {
            fs::copy(entry.path(), new_path)?;
        }
    }

    for thy in user_theories {
        if !processed.contains(thy) {
            println!("WARNING: Listed theory {:?} was not found.", thy);
        }
    }

    Ok(processed)
}

fn begin_snippet(name: &str) -> String {
    vec!["\\", BEGIN, "{", name, "}{%"].join("")
}

fn end_snippet() -> String {
    vec!["}%", END].join("")
}

fn iname(prefix: &Option<String>, n: &str, i: usize) -> String {
    match prefix {
        Some(pre) => format!("{}:{}-{}", pre, n, i),
        None => format!("{}-{}", n, i),
    }
}

fn extract_snippets(path: &Path, theories: &[OsString]) -> io::Result<String> {
    let mut snippets: Vec<String> = vec![];

    let disambiguate = theories.len() > 1;

    for entry in WalkDir::new(path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| has_ext(e.path(), "tex"))
        .filter(|e| {
            theories.contains(
                &e.path()
                    .file_stem()
                    .expect("Could not get file stem.")
                    .to_os_string(),
            )
        })
    {
        let prefix = if disambiguate {
            let theory = entry
                .path()
                .file_stem()
                .expect("Could not get file stem.")
                .to_str()
                .expect("Could not convert to str.");
            Some(escape_underscores(theory))
        } else {
            None
        };

        let mut including = false;
        let file = fs::File::open(entry.path())?;
        let lines = io::BufReader::new(file).lines();

        let mut name = String::new();
        let mut i = 0;

        for line in lines.filter_map(|l| l.ok()) {
            if line.contains(BEGIN) {
                including = true;
                let words: Vec<_> = line.split_whitespace().collect();
                name = words[1].to_string();
                i = 0;
                snippets.push(begin_snippet(&iname(&prefix, &name, i)));
            } else if line.contains(END) {
                including = false;
                snippets.push(end_snippet());
            } else if including {
                snippets.push(line.clone());
            }

            if including && line.contains(ISA_NEWLINE) {
                snippets.push(end_snippet());
                i += 1;
                snippets.push(begin_snippet(&iname(&prefix, &name, i)));
            }
        }
    }

    Ok(snippets.join("\n"))
}

const OPTIONS: [&str; 3] = ["-quick_and_dirty", "-quick-and-dirty", "-library"];

fn main() {
    let mut args: Vec<String> = env::args().collect();

    if args.len() < 3 {
        println!(
            "Usage: ./{} theory/root snippets-out.tex [optional list of theories to include]",
            args[0]
        );
        exit(1);
    }

    let quick_and_dirty = args.contains(&String::from("-quick_and_dirty"))
        || args.contains(&String::from("-quick-and-dirty"));

    let library = args.contains(&String::from("-library"));

    args.retain(|x| !OPTIONS.contains(&x.as_str()));

    let mut user_theories = args.iter().skip(3).map(OsString::from).collect::<Vec<_>>();

    let isa_path = Path::new(&args[1]);
    if !isa_path.exists() {
        println!(
            "The given Isabelle file or directory does not exist: {}",
            isa_path.display()
        );
        exit(1);
    }

    let temp_dir = tempdir().expect("Could not create a temporary directory.");
    let temp_path = temp_dir.path();

    println!("Working directory: {}", temp_path.display());

    if isa_path.is_file() {
        let theory =
            mkroot(isa_path, temp_path, library).expect("Error making theory root directory.");
        user_theories.push(theory);
    } else {
        let processed = copy_isabelle(&isa_path, &temp_path, &user_theories)
            .expect("Could not copy Isabelle files.");
        if user_theories.is_empty() {
            user_theories.extend(processed);
        }
    }

    let mut isa_args = vec![
        "build",
        "-c",
        "-D",
        ".",
        "-o",
        "document=pdf",
        "-o",
        "document_output=output",
    ];

    if quick_and_dirty {
        isa_args.extend(&["-o", "quick_and_dirty"]);
    }
    call_isabelle(temp_path, &isa_args).expect("Error running Isabelle build.");

    println!("Extracting snippets for theories: {:?}", user_theories);

    let snippets =
        extract_snippets(&temp_path, &user_theories).expect("Could not extract snippets.");

    let snips_path = Path::new(&args[2]);
    fs::write(snips_path, snippets).expect("Could not write to snippets file.");

    println!("Snippets written to: {}", snips_path.display());
}

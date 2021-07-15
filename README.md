isasnips
========

This tool processes Isabelle/HOL theory files into LaTeX snippets.

The `isabelle` binary must be available on your PATH along with anything needed to run `isabelle build`.

Running the tool
----------------

There are two ways to run the tool: on a single theory and on a session.

### Single theory

```
isasnips Theory.thy out.tex
```

This will set up a default Isabelle session for `Theory.thy`, process it and output the snippets to `out.tex`.

This assumes that `Theory.thy` does not import anything special or require any LaTeX packages that are not included by `isabelle mkroot`.

### Session

```
isasnips session-dir out.tex [Theory1 Theory2 ...]
```

This will copy the given `session-dir` to a temporary location, process the named theories and extract their snippets to `out.tex`.
If no list of theories is given, then every theory is processed and extracted.

This assumes that `session-dir` includes a `ROOT` file and everything so that it can be succesfully build by `isabelle build`.

The (copy of the) session is cleaned before building.

If snippets are generated for more than one theory then the snippets are prefixed by the name of the theory.


### Unfinished theories

If one of your Isabelle theories contains a `sorry`, you will need to pass the option `-o quick_and_dirty` to Isabelle before it will compile your session.
To do this, you can pass the option `-quick_and_dirty` to isasnips.

Output
------

The tool preprocesses the given theories by marking every line of the input files.
It then runs the `isabelle build` tool to generate LaTeX for the session and extracts snippets from the generated LaTeX.

Each snippet is named by:

0. The theory name if there is more than one.
1. The command name.
2. A name extracted from the theory or a hash value of the content.
3. A relative line number.

```
[Theory:]command:name-lineno
```

Underscores are converted to hyphens for the snippet names.
Symbols are stripped to their ASCII name e.g. `pi`.

### Examples

The following datatype declaration:

```
datatype ('a, 'b) either = Left 'a | Right 'b
```

Currently generates the following snippet:

```
\DefineSnippet{datatype:either-0}{%
\isacommand{datatype}\isamarkupfalse%
\ {\isacharparenleft}{\isacharprime}a{\isacharcomma}\ {\isacharprime}b{\isacharparenright}\ either\ {\isacharequal}\ Left\ {\isacharprime}a\ {\isacharbar}\ Right\ {\isacharprime}b%
}%EndSnippet
```

The following anonymous lemma:

```
lemma ‹2 + 2 = 4› by simp
```

Gets a name like so:

```
\DefineSnippet{lemma:fe3e5fffe22de733-0}{%
```

Definitions and abbreviations are named correctly without having to give an explicit name:

```
definition "π ≡ 3"
```

```
\DefineSnippet{definition:pi-0}{%
\isacommand{definition}\isamarkupfalse%
\ {\isachardoublequoteopen}{\isasympi}\ {\isasymequiv}\ {\isadigit{3}}{\isachardoublequoteclose}%
}%EndSnippet
```

Recommended LaTeX
-----------------

The style files generated by `isabelle latex -o sty` are needed to compile the snippets.

Something like the following macros is needed to turn snippets into LaTeX commands:

```
\usepackage{isabelle, isabellesym}

\isabellestyle{it} % optional
\newcommand{\DefineSnippet}[2]{\expandafter\newcommand\csname snippet--#1\endcsname{#2}}
\input{snips}

% Include every line of a snippet:

\newcommand{\Snippet}[1]{{%
  \newcount\i
  \i=0
  \loop
    \csname snippet--#1-\the\i\endcsname
    \advance \i 1
  \ifcsname snippet--#1-\the\i\endcsname
  \repeat
}}

% Include only a part, e.g. lines 3-5 (starting from 0):

\newcommand{\SnippetPart}[3]{{%
  \newcount\i
  \i=#1
  \loop
    \ifnum \i=#2
      \renewcommand{\isanewline}{}%
    \fi
    \csname snippet--#3-\the\i\endcsname
    \advance \i 1
    \ifnum \i>#2 {}
    \else \repeat
}}

```

Depending on your LaTeX template, you may also need the following lines, since Isabelle will sometimes generate macros that are not defined in a template:
```
% Isabelle currently generates some undefined macros, so we just define them to be empty:
\def\isadelimtheory{}\def\endisadelimtheory{}
\def\isatagtheory{}\def\endisatagtheory{}
\def\isadelimML{}\def\endisadelimML{}
\def\isatagML{}\def\endisatagML{}
\def\isafoldML{}
\def\isadelimproof{}\def\endisadelimproof{}
\def\isatagproof{}\def\endisatagproof{}
\def\isafoldproof{}
```

### Examples

```
\begin{isabelle}
    \Snippet{datatype:either}
\end{isabelle}
```

```
\begin{isabelle}
    \SnippetPart{3}{5}{theorem:long-theorem}
\end{isabelle}
```

Limitations
-----------

- The parser is ad hoc and guaranteed to do something unexpected in some cases.
- I do not know how to make Isabelle generate LaTeX without subsequently compiling it, so your theory/session must allow for this.


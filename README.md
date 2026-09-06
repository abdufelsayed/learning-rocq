# Learning Rocq

I'm working through Software Foundations Volume 1: Logical Foundations to learn Rocq and get more practice with formal proofs.

This is where I keep the code I write while following along, my attempts at the exercises, and notes on what I'm learning.

## Learning materials

- [Logical Foundations, part of Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current)
- [Rocq tutorial video playlist](https://www.youtube.com/playlist?list=PLre5AT9JnKShFK9l9HYzkZugkJSsXioFs)

## Chapters

I've organized the work by chapter under `src`. Each chapter source file contains
the examples and exercises in book order, with tests and notes alongside it when
they exist.

| Chapter | Code and exercises | Notes |
| --- | --- | --- |
| Basics | [Basics.v](src/Basics.v) | [BasicsNotes.md](src/BasicsNotes.md) |

## Compiling

From the repository root:

```sh
make
```

The Makefile maps `src` to the `LF` namespace and discovers the Rocq source
files in that directory. To compile one file directly, use:

```sh
rocq compile -Q src LF src/Basics.v
```

To remove compiled Rocq artifacts and generated Makefile metadata:

```sh
make clean
```

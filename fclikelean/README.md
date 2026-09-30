# Prospective Formal Conjectures statement

This directory contains an unofficial draft of Littlewood's mutually touching
infinite cylinders problem in the style of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures).

It has not been submitted, reviewed, approved or merged. The proposed destination is
`FormalConjectures/Other/LittlewoodCylinders.lean`.

## File

[`LittlewoodCylinders.lean`](LittlewoodCylinders.lean) contains one declaration,
`LittlewoodCylinders.littlewood_cylinders`. In accordance with the intended submission
style, the full mathematical statement is in the theorem itself; it does not depend on
project-local helper definitions.

The two occurrences of `sorry` are intentional in this statement draft:

- `answer(sorry)` leaves the yes/no answer open;
- `by sorry` is the placeholder proof expected for an open problem statement.

The completed proof of the same inlined statement is in [`../lean`](../lean),
where the final theorem reports only `[propext, Classical.choice, Quot.sound]`.
This directory remains a separate proposed-statement draft with intentional
placeholders; it is not the proof entry point and has not been submitted to the
Formal Conjectures repository. Its `research open` tag is the draft's original
metadata, not a report on the completed local proof.

## Local check

Copy the file into a Formal Conjectures checkout as
`FormalConjectures/Other/LittlewoodCylinders.lean`, then run:

```bash
lake --wfail build FormalConjectures.Other.LittlewoodCylinders
```

This repository pins the Formal Conjectures commit used by the proof scaffold in
[`../lean/lakefile.toml`](../lean/lakefile.toml).

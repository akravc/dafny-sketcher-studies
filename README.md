# dafny-sketcher-studies

A repository for the studies on semi-automated Dafny proof completion using [dafny-sketcher](https://github.com/namin/dafny-sketcher).

## Repository Structure

```
dafny-sketcher-studies/
├── README.md             # This file - project documentation
├── challenges/           # Dafny verification challenges for dafny-sketcher/vfp
├── issues/               # Issues and bug reports 
└── solutions/            # Solutions to the challenges
```

### Contents

#### `/challenges/`
Contains Dafny verification challenges and exercises.
- `BST.dfy`: classic lemmas about a binary search tree.
- `BSTModular.dfy`: the modular implementation of `BST.dfy`.

#### `/issues/`
Stores known issues and bug reports.

#### `/solutions/`
Houses solutions to the challenges in the `/challenges/` directory.
- `BSTClaude.dfy`: Claude's solution for `BST.dfy`.
- `BSTMinimal.dfy`: a streamlined version of Claude's solution, including notes about which parts ended up being necessary for the proof.


## Resources

- [Dafny-Sketcher GitHub Repository](https://github.com/namin/dafny-sketcher) - interactive semi-automated verified program synthesis tool for Dafny.
- [Dafny GitHub Repository](https://github.com/dafny-lang/dafny)
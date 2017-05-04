Removed features
================

This version of the source code was cleaned up to be as close as possible to the
ICFP'12 published version.  In the process some features added in later papers
were removed with a view that we might want to restore them someday.  Here's a
list of what was removed together with relevant commit hash.

  * **Compact** (40e38ed2) - whole module removed

  * **with-syntax** (e2fd6e38) - allowed providing explicit environment

  * **labels** (cf666522) - note that this commit also does some silly changes
      to `Eval` that were later reverted by 1115a1e0

  * **`TraceVar` and `TraceUpd` primitives** (dcaaa81d)

  * **`as` primitive** (8738af1d) - only partial implementation

  * **`replay` primitive** (96a83ec1)

  * **`dep`, `expr`, and `where` primitives** (38b6ef8c) - removed the whole
      `Annot` module

  * **`profile`, `profileDiff` and `treesize` primitives** (f90b8df6)

  * **`visualize` and `visualizeDiff` primitives** (039bdea6)

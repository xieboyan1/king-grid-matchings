# Counting perfect matchings on the king’s grid in Lean 4

[中文说明](README.zh-CN.md)

Read the manuscript [Perfect matchings with two axial edges on the king’s grid](paper/main.pdf), or compile its [self-contained LaTeX source](paper/main.tex) with Tectonic or two passes of pdfLaTeX. The bibliography and strip diagrams are embedded in the source.

Pair every cell of a rectangle with one of its eight neighbors. The boundary is free, and two diagonal edges may cross. How many matchings use exactly two horizontal or vertical edges? On a $2n\times 2n$ square there are $n^2(n+1)$. For example, there are 12 on a $4\times4$ board and 80 on an $8\times8$ board.

## Theorems

Write $A_j(m,n)$ for the number of perfect matchings of a $2m\times 2n$ board with exactly $j$ horizontal or vertical edges **in total**. All other edges are diagonal. For all natural numbers $m,n$,

$$
A_0(m,n)=1,\qquad A_2(m,n)=n\binom{m+1}{2}+m\binom{n+1}{2}.
$$

Ryłko recorded the square cases as conjectures. In his notation the board has $2n^2$ matching edges and $T(n,k)$ counts matchings with $2k$ diagonals. Thus $A_0(n,n)=T(n,n^2)$ and, for $n\ge1$, $A_2(n,n)=T(n,n^2-1)$. The literature notes give an earlier theorem implying $A_0$ and the classical permutation result used in the $A_2$ argument. [OEIS A401673](https://oeis.org/A401673) · [Related work](docs/related-work.md)

| Lean declaration | What the kernel checks |
| --- | --- |
| `DimerDiagonal.exactly_one_diagonal_tiling` | On the finite rectangle there is exactly one partner map pairing every cell diagonally. [Source](KingGrid/Diagonal.lean) |
| `KingEnumeration.exactly_two_rectangle` | A duplicate-free list contains precisely the geometric matchings with two axial edges. Twice its length is $nm(m+1)+mn(n+1)$. [Source](KingGrid/KingEnumeration.lean) |
| `KingEnumeration.exactly_two_square` | The same enumeration on a square has length $n^2(n+1)$. [Source](KingGrid/KingEnumeration.lean) |

## Reproduce the proofs

From the repository root, with Lean 4.19.0 and Python 3.8 or later installed, run the commands below. With elan installed, the checked-in `lean-toolchain` selects the Lean release. The proof imports only libraries shipped with Lean. [Lean installation instructions](https://lean-lang.org/install/)

```sh
lake build
python scripts/verify.py
python scripts/check_small_boards.py
```

The first command builds the library. The second copies the sources into a fresh temporary directory, compiles them with `--trust=0`, and audits the axioms reported for all three public theorems and the named supporting results. The final line should be `PASS: 11 modules, 29 axiom reports.` To select a standalone Lean executable, pass `--lean /path/to/lean`. To save the output, add `--report audit.txt`. On systems where Python 3 is named `python3`, use that command. [Sample audit](docs/verification.txt)

The last command independently enumerates small boards by pairing the first uncovered cell. It checks 25 rectangles with $0\le m,n\le4$, including the empty board and both orientations of nonsquare rectangles. It prints $A_2(2,3)=21$ for the $4\times6$ board. The GitHub Actions workflow runs the build and both checks on pushes and pull requests. [Workflow](.github/workflows/verify.yml)

To inspect a public theorem in a Lean file in this project:

```lean
import KingGrid

#check DimerDiagonal.exactly_one_diagonal_tiling
#check KingEnumeration.exactly_two_rectangle
#print axioms KingEnumeration.exactly_two_square
```

## Why the formula holds

1. **The two axial edges are parallel.** There are equally many cells in even and odd rows. Each nonhorizontal edge covers one of each. Consequently there are equally many horizontal edges in even and odd rows. The same argument with columns gives an even number of vertical edges. Two axial edges must therefore both be horizontal or both vertical. [Board cuts](KingGrid/BoardCuts.lean)
2. **Columns pair off.** In the horizontal case every cell in column 1 has its partner in column 2. Those partners exhaust column 2. Repeat on the remaining columns. The board splits into $n$ independent strips of width two. Within a strip the top two cells either pair horizontally or each takes the opposite cell in the next row, forming a cross. Thus a strip is a word of single rows and double rows. [Strip geometry](KingGrid/StripGeometry.lean)
3. **Count the exceptional strip.** A strip of even height has an even number of single rows. With two horizontal edges, exactly one strip has two singles and all others consist of crosses. The exceptional strip has two singles and $m-1$ crosses, so choosing the two positions of the singles among $m+1$ positions determines it. This gives $n\binom{m+1}{2}$ horizontal matchings. Transposition gives $m\binom{n+1}{2}$ vertical ones. With zero axial edges every strip consists entirely of crosses. If a dimension is zero, the empty matching gives the stated formulas. The one-strip count is the classical enumeration of Fibonacci permutations. [Diaconis, Graham and Holmes, §2.4](https://doi.org/10.1214/lnms/1215090070)

In the two-edge proof, Lean builds matchings from strip words and recovers the strip words from any legal matching. Turning an edge around or reordering the edge list preserves the same undirected relation. The round trip and the duplicate-free enumeration justify counting these relations. The zero-edge Lean proof gives a separate uniqueness argument using the canonical partner map. [Placement](KingGrid/StripPlacement.lean) · [Encoding](KingGrid/BoardEncoding.lean) · [Round trip](KingGrid/BoardRoundtrip.lean)

## Provenance and license

This project grew out of an AI-assisted investigation. Codex assisted with literature discovery, construction of the arguments, implementation of the Lean proofs, and drafting the documentation. The checked declarations and the bibliography are available for inspection. The [MIT license](LICENSE) applies to the verification software and its documentation. The manuscript in `paper/` is separate from this software license.

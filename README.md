# On Symmetric Rank Decompositions of the 3x3 Matrix Multiplication Tensor

All tensor decompositions here are mod 2.

### Part 1
* [(link)](https://murj-assets.s3.amazonaws.com/assets/issues/Vol_43_Published.pdf#page=33)
* [Source code (a single Java file)](https://github.com/coolcomputery/Matrix-Multiplication-Tensor-Decomposition/blob/79500ae287090ac08c502425727eb56ccbad86fe/SymmetricMod2.java)
* Considers cyclic + (permutation-matrix de Groote) symmetries of the matrix multiplication tensor

## Part 2
* [(link)](https://murj-assets.s3.amazonaws.com/assets/issues/Vol_45_Published.pdf#page=33) (has the same title in this print)
* [***Full report with omitted tables showing search results***](https://github.com/coolcomputery/Matrix-Multiplication-Tensor-Decomposition/blob/4508649a56a2861fd3a262c1159feba959d48d60/full-part2-report.pdf)
* [Source code](https://github.com/coolcomputery/Matrix-Multiplication-Tensor-Decomposition/tree/5b15fedf474cb35f6b43b360b05aadc0520fb4af)
  * `SymmetricMod2.java` searches for decompositions satisfying a given symmetry group
  * `MatrixTripletTransformations.java` enumerates symmetry groups that superset a given subset
* Considers cyclic + transpose + (all de Groote) symmetries

#### Notation of symmetry subgroups
A subgroup is represented as a comma-delineated list of generators (no spaces)
* the cyclic shift function $\bigtriangleup$ is denoted as `cyc`
* the transpose function $\intercal$ is denoted as `tp`
* the sandwiching function $\phi_{X,Y,Z}$ is denoted as `tr<X>-<Y>-<Z>`, with each of $X$, $Y$, and $Z$ written in row-major order of its elements
* function composition is denoted as `@`

Ex. the subgroup below is denoted as `cyc,tr110010001-100010001-100010001@cyc@tp`:
```math
\langle
\bigtriangleup , \phi_{\left[\begin{smallmatrix}1&1&0\\0&1&0\\0&0&1\end{smallmatrix}\right] , \left[\begin{smallmatrix}1&0&0\\0&1&0\\0&0&1\end{smallmatrix}\right] , \left[\begin{smallmatrix}1&0&0\\0&1&0\\0&0&1\end{smallmatrix}\right]} \circ \bigtriangleup \circ \intercal
\rangle
```

#### `SymmetricMod2`
* Command line: `java -Xmx30g src/SymmetricMod2.java * *`..., where each `*` notates a symmetry subgroup, and the `*` are separated by spaces
  * For each notated subgroup $G$, this command will exhaustively search for all mod 2 decompositions of the $\mathcal{T}^{\langle 3, 3, 3\rangle}$ tensor of rank $\le R$ that are $G$-invariant, where $R$ is at most 23 but is otherwise set to be as high as the search will be feasible for.
    * The exact notion of feasibility can be changed by editing the source code.

#### `MatrixTripletTransformations`
  * `generatingSetsAdd1_mod_conj(gset)`, where `gset` notates a set of generators $S$, returns all subgroups of the form $\langle S \cup \{f\}\rangle$ for all $f$ in the universe group $\Gamma$, **distinct up to conjugacy**.

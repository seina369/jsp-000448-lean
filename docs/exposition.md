# How many vertices force a monochromatic tree? An exposition

*An account, for readers who know what a graph is, of the results formalized in
`JSP448.lean`. Nothing here is new mathematics.*

## The question

Colour every edge of the complete graph `K_N` with one of `r` colours. If `N` is
large, some colour must contain a copy of any tree `T` you fix in advance. The
smallest such `N` is the `r`-colour Ramsey number `R_r(T)`.

For complete graphs these numbers grow exponentially and are famously unknown. For
trees, Erdős and Graham asked in 1975 whether they are as small as they could
reasonably be: about `r` times the number `n` of vertices of the tree.

## Why `r·n` is the natural guess

Let `T` have `k = n − 1` edges. A graph with *minimum* degree `k` contains `T`
greedily. The Erdős–Sós conjecture — now a theorem, with a machine-checked proof —
says that *average* degree above `k − 1` is already enough:

> a graph on `N` vertices with more than `(k − 1)N/2` edges contains every tree with
> `k` edges.

Now count. `K_N` has `N(N − 1)/2` edges, shared among `r` colours. If no colour
contained its tree, each colour would have at most `(k − 1)N/2` edges, so

    N(N − 1)/2 ≤ r (k − 1) N / 2,   i.e.   N ≤ r(k − 1) + 1.

Hence **`R_r(T) ≤ r(k − 1) + 2`**: slope `r` in the size of the tree, for every
tree and every number of colours. (`ramseyNumber_tree_le_tight`.)

The same count lets each colour look for a different tree: with `kᵢ` edges in
colour `i`, `∑(kᵢ − 1) + 2` vertices suffice
(`multicolor_ramsey_trees_asym_tight`).

## One vertex fewer, by parity

Take `N = r(k − 1) + 1` exactly. The count above is then tight: every colour would
need exactly `(k − 1)N/2` edges. If `r` and `k` are both even, `k − 1` and `N` are
both odd, and `(k − 1)N/2` is not a whole number. So some colour contains its tree
after all: **`R_r(T) ≤ r(k − 1) + 1`** in that case
(`ramseyNumber_tree_le_parity`).

## Can the bound be beaten? Three colourings say no

To show `R_r(T) > N` one must colour `K_N` with no monochromatic `T`.

**Stars, `k` odd — the clock colouring.** Put `N = r(k − 1) + 1` points on a
circle. The distance between two points is a number from `1` to `(N − 1)/2`. Cut
that range into `r` consecutive blocks of `(k − 1)/2` distances and colour an edge
by the block of its distance. Each point sees two points at each distance, so
exactly `k − 1` neighbours in each colour — one too few to be the centre of a star
with `k` edges.

**Stars, `k` even — the tournament schedule.** When `N` is even, `K_N` splits into
`N − 1` rounds in which everybody is paired off (a round-robin schedule: one player
sits at the centre, the others rotate). Give each colour `k − 1` rounds. Again each
point has at most `k − 1` neighbours per colour.

Together with the two upper bounds this determines the star completely
(Burr–Roberts): **`R_r(K_{1,k}) = r(k − 1) + 1` if `r` and `k` are both even, and
`r(k − 1) + 2` otherwise** (`ramseyNumber_star_all`).

**Every tree — the grid colouring.** Let `p` be prime and take the `p × p` grid
with coordinates mod `p`. Colour an edge by the *slope* of the line through its two
points: `p` ordinary slopes and "vertical", `p + 1` colours. Edges of one colour
join points on the same line of that slope, and such a line has only `p` points. A
tree is connected, so a monochromatic copy would sit inside one line — impossible
for a tree with `p + 1` vertices. So `p²` vertices are not enough, while the upper
bound with `r = p + 1`, `k = p` is `(p + 1)(p − 1) + 2 = p² + 1`:

> **every tree with `p` edges has `R_{p+1}(T) = p² + 1`**, whatever its shape
> (`ramseyNumber_tree_eq_of_prime`).

This is the simplest instance of Erdős and Graham's own lower bound, which uses
more general block designs in place of the affine plane.

## What remains

The upper bound `R_r(T) ≤ r·n − 2r + 2` is therefore sharp for stars and, for
suitable numbers of colours, for every tree. It is *not* an equality for every
tree and every `r`: with two colours the path on `n` vertices has Ramsey number
only about `3n/2` (Gerencsér–Gyárfás). The exact value of `R_r(T)` for general
trees and general `r` is open.

## What "formalized" means here

Each statement above is a theorem in the proof assistant Lean 4, checked down to
the axioms of mathematics by a small trusted kernel. The Erdős–Sós theorem is
imported from an existing formalization (`tadamcz/erdos548`); the counting
arguments, the three colourings and the exact values are in `JSP448.lean`.

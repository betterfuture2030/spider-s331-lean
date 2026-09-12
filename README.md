# Lean 4 formalisation: a fixed-part bipartite extremal bound for the eight-vertex spider

Machine-checked proof (Lean 4 + Mathlib) of the results in

> Peter Lowes, *A Fixed-Part Bipartite Extremal Bound for the Eight-Vertex Spider*,
> Zenodo, version 1.0 (3 August 2026), doi:[10.5281/zenodo.21783225](https://doi.org/10.5281/zenodo.21783225).

Let `T = S(3,3,1)` be the tree obtained from the seven-vertex path `P₇` by attaching one leaf to
its central vertex. The paper proves that every bipartite graph `G` with `e(G) > 2·v(G)` contains
`T`, hence `ex_bip(m, n; T) ≤ 2(m + n)` for all part sizes `m, n`, which is the case of the
Waite–Aydin fixed-part conjecture (arXiv:2607.29579, Conjecture 1.3) for the smallest tree outside
the scope of their Theorem 1.4; Section 7 shows that `S(3,3,1)` is the *only* tree on at most nine
vertices outside that scope.

Every statement below is proved without `sorry`, without `native_decide`, and depends only on
Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); see
[`CERTIFICATE.md`](CERTIFICATE.md).

## Paper ↔ Lean

| Paper | Lean declaration | File |
|---|---|---|
| Lemma 3.1 (3-core reduction) | `Spider.core` | `Spider/Basic.lean` |
| eq. (3.1) (deleting a vertex of degree `d`) | `Spider.dsum_erase` | `Spider/Basic.lean` |
| eq. (3.2) and the averaging step | `Spider.exists_five_nbr` | `Spider/Basic.lean` |
| Lemma 4.1 (rooted embedding lemma) | `Spider.hasSpiderAt_of_three_five` | `Spider/Basic.lean` |
| Path-assembly step inside Lemma 4.1 | `Spider.hasSpiderAt_of_path` | `Spider/Basic.lean` |
| **Theorem 1.1** (explicit copy of `T`) | `Spider.main` | `Spider/Basic.lean` |
| **Theorem 1.1** (`spider ⊑ G`, Mathlib containment) | `Spider.spider_isContained` | `Spider/Extremal.lean` |
| **Theorem 1.1**, order form `ex_bip(N; T) ≤ 2N` | `Spider.edge_bound`, `Spider.edge_bound_of_colorable` | `Spider/Extremal.lean` |
| **Theorem 1.1**, fixed-part form `ex_bip(m,n;T) ≤ 2(m+n)` | `Spider.exbip_le` | `Spider/Extremal.lean` |
| Remark 4.2 (`K₄,₄` is `T`-free) | `Spider.spider_free_K44` | `Spider/Sharpness.lean` |
| Proposition 6.1, `ex_bip(4,4;T) = 16` | `Spider.exbip_four_four` | `Spider/Sharpness.lean` |
| Proposition 6.1, `q·K₄,₄` attains `2N` for `N = 8q` | `Spider.exbip_eq_of_qK44` | `Spider/Sharpness.lean` |
| Proposition 6.1, `ex_bip(m,n;T) ≥ 2(m+n) − 8` | `Spider.exbip_ge`, `Spider.exbip_within_eight` | `Spider/AdditiveGap.lean` |
| Lemma 7.1 (leaves in `A`; `σ ≥ ⌈(a−b+1)/b⌉`) | `Spider.card_leaves_add`, `Spider.sigma_lower` | `Spider/Census.lean` |
| Proposition 7.2 (`S(3,3,1)` is the unique tree on `≤ 9` vertices with `σ < min{a−b, b−1}`) | `Spider.census`, `Spider.spider_outside_criterion` | `Spider/Census.lean` |
| **Corollary 1.2** (Conjectures 1.2/1.3 for all trees on `≤ 9` vertices), *conditional on Waite–Aydin* | `Spider.corollary_nine`, `Spider.corollary_nine_order` | `Spider/Census.lean` |

Remark 7.3 (the computer enumeration for ten and eleven vertices) is not a theorem of the paper
and is not formalised.

### How the statements are phrased

* A graph is a Mathlib `SimpleGraph V` on a finite vertex type `V` with decidable adjacency.
* Bipartiteness is a proper 2-colouring `c : V → Bool` with `G.Adj u w → c u ≠ c w`
  (`edge_bound_of_colorable` accepts Mathlib's `G.Colorable 2` instead). For the fixed-part
  form the host is a graph on `Fin m ⊕ Fin n` whose every edge joins the two summands.
* `e(G)` is `#G.edgeFinset`, `v(G)` is `Fintype.card V`.
* `Spider.spider : SimpleGraph (Fin 8)` is the concrete tree (centre `0`, arms `0-1-2-3`, `0-4-5-6`,
  leaf `7`); `spider ⊑ G` is Mathlib's `SimpleGraph.IsContained` (an injective homomorphism, i.e.
  a not-necessarily-induced copy) and `spider.Free G` its negation. `Spider.HasSpiderAt G v` is
  the explicit eight-distinct-vertices form of "contains a copy of `T` centred at `v`".
* In Section 7 a tree is a Mathlib `SimpleGraph.IsTree`; its bipartition is a proper 2-colouring
  `c`, the class `B` is `Spider.cls c b`, `A` is `Spider.cls c (!b)`, `S_T(x)` is
  `Spider.pendantSet T x` and `σ(T_{a,b})` is `Spider.sigma T c b`. Proposition 7.2 concludes with
  a graph isomorphism `T ≃g spider`.
* Corollary 1.2 rests on Waite–Aydin's Theorem 1.4 and Corollary 4.8, which are external results.
  They are stated verbatim as the explicit hypotheses `Spider.WaiteAydinThm14` and
  `Spider.WaiteAydinCor48` (with the bound `Spider.waBound`, resp. `Spider.waOrderBound2`), and
  the corollary is proved *assuming* them. Nothing else in the development is assumed.

## Reproducing the check

```bash
# install elan (Lean version manager) if needed: https://github.com/leanprover/elan
cd lean/spider-s331
lake exe cache get     # fetch the prebuilt Mathlib oleans (avoids a multi-hour Mathlib build)
lake build --wfail     # compiles all five modules, warnings promoted to errors; no output = no errors
lake env lean Spider/Certificate.lean   # prints the axioms each headline theorem depends on
```

Toolchain: `leanprover/lean4:v4.33.1`; Mathlib pinned to tag `v4.33.1` in `lake-manifest.json`.
The GitHub Actions workflow `.github/workflows/lean-spider.yml` performs the same check on every
push touching this directory.

# Verification certificate

Formal verification of

> P. Lowes, *A Fixed-Part Bipartite Extremal Bound for the Eight-Vertex Spider*,
> Zenodo, version 1.0 (3 August 2026), doi:10.5281/zenodo.21783225

in Lean 4 with Mathlib. Generated on 2026-09-12 00:20 UTC from a clean checkout of this
directory (`lake exe cache get && lake build --wfail`).

## Scope

Formalised in full: Theorem 1.1 (all four phrasings), Lemma 3.1, equations (3.1)–(3.2), Lemma 4.1,
Remark 4.2, Proposition 6.1 (both parts), Lemma 7.1 and Proposition 7.2 (including the converse:
`S(3,3,1)` is a tree with `σ = 1 < 2`). Corollary 1.2 is formalised *conditionally*: it takes the
external Waite–Aydin results (arXiv:2607.29579, Theorem 1.4 and Corollary 4.8) as explicit
hypotheses (`Spider.WaiteAydinThm14`, `Spider.WaiteAydinCor48`). Remark 7.3 (a computer
enumeration) is not a theorem and is not formalised.

## Environment

| Item | Value |
|---|---|
| Lean | `Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)` |
| Lake | `Lake version 5.0.0-src+819816b (Lean version 4.33.1)` |
| Mathlib | tag `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474` |
| Platform | `x86_64-linux` |

## Build

`lake build --wfail` (warnings promoted to errors): **Build completed successfully**, 0 errors,
0 warnings. The sources contain no `sorry`, no `native_decide` and no `axiom` declarations:

```
Spider/Certificate.lean:6:Printing the axioms used by the headline theorems. A sound, `sorry`-free development uses only
```

## Axioms

Output of `lake env lean Spider/Certificate.lean`. Every headline theorem is closed under exactly
the three standard axioms of Lean's kernel (no `sorryAx`, no custom axioms):

```
'Spider.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.spider_isContained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.edge_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.edge_bound_of_colorable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.exbip_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.spider_free_K44' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.exbip_four_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.spider_free_qK44' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.card_edgeFinset_qK44' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.exbip_eq_of_qK44' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.spider_free_gapGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.card_edgeFinset_gapGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.exbip_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.exbip_within_eight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.card_leaves_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.sigma_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.census' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.spider_isTree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.spider_outside_criterion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.corollary_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spider.corollary_nine_order' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Source hashes (SHA-256)

```
afdb3cfe72ce40c95b30d191574ed02fa9faab10f7867c021460027ef1e832e0  Spider.lean
beb149353058f54ba15d52815111bd92c22c35eff31c53e2d48c4d08fc4b13b9  Spider/AdditiveGap.lean
c768e26657ccbc3a5464f165a1da75f2dd9ccf89b9e7532f914e0717f07ea620  Spider/Basic.lean
26290b85f7ab08d1a069215ca1fe0033bf42e92e90b132f78f7c75b3224fa4ef  Spider/Census.lean
6660cadb49278982c7f638abb3d6544c9a1f620b313e091da07d444cde3c6da8  Spider/Certificate.lean
28c6ab9e42e06c39cee6ce89bab5ec23bd4945116610ecb32328e04f1b6f2575  Spider/Extremal.lean
c1db825a14ad1160beac6904c7746c54f4b895f7d1b14e2e27368fcc81d4be30  Spider/Sharpness.lean
b0d6cff6edb0887979df5bb0307d40997c1c5e19bdd42f4af5bcae2747484534  lakefile.toml
825c69666f3395c52bb965d1828e8f21df52a583827188cd37be477762918d10  lake-manifest.json
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
```

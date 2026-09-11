# Verification certificate

Formal verification of *A fixed-part bipartite extremal bound for the eight-vertex spider*
(P. Lowes, draft of 3 August 2026) in Lean 4 with Mathlib.

Generated on 2026-09-11 23:33 UTC from a clean checkout of this directory
(`lake exe cache get && lake build --wfail`).

## Environment

| Item | Value |
|---|---|
| Lean | `Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)` |
| Lake | `Lake version 5.0.0-src+819816b (Lean version 4.33.1)` |
| Mathlib | tag `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474` |
| Platform | `x86_64-linux` |

## Build

`lake build --wfail` (warnings promoted to errors): **Build completed successfully**, 0 errors,
0 warnings, 0 `sorry`, no `native_decide`.

```
(no occurrences of sorry / native_decide in the sources)
```

## Axioms

Output of `lake env lean Spider/Certificate.lean` (each headline theorem is closed under
exactly the three standard axioms of Lean's kernel, i.e. no `sorryAx`, no custom axioms):

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
```

## Source hashes (SHA-256)

```
df14777bfde0fef2826522f0bd41420e337955b89ac190b248931a03bea2916b  Spider.lean
beb149353058f54ba15d52815111bd92c22c35eff31c53e2d48c4d08fc4b13b9  Spider/AdditiveGap.lean
4202ecac11667c499309e46170c050d577b79dd795692474cf270e2eccf28381  Spider/Basic.lean
ef6e056d2fd621442fd4189b0814461e118aaa391f766c4d3a250587cff7806a  Spider/Certificate.lean
28c6ab9e42e06c39cee6ce89bab5ec23bd4945116610ecb32328e04f1b6f2575  Spider/Extremal.lean
c1db825a14ad1160beac6904c7746c54f4b895f7d1b14e2e27368fcc81d4be30  Spider/Sharpness.lean
b0d6cff6edb0887979df5bb0307d40997c1c5e19bdd42f4af5bcae2747484534  lakefile.toml
825c69666f3395c52bb965d1828e8f21df52a583827188cd37be477762918d10  lake-manifest.json
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  lean-toolchain
```

import Spider.Basic

/-!
# The extremal bound in Mathlib's language

We package the eight-vertex spider as a concrete `SimpleGraph (Fin 8)` and restate the main
theorem using Mathlib's containment relation `⊑` (`SimpleGraph.IsContained`: existence of an
injective graph homomorphism, i.e. a not-necessarily-induced subgraph copy) and `Free`.

* `Spider.spider_isContained` — Theorem 1.1: a bipartite graph with `e(G) > 2·v(G)` contains `T`.
* `Spider.edge_bound` — the contrapositive: a `T`-free bipartite graph has `e(G) ≤ 2·v(G)`,
  i.e. `ex_bip(N; T) ≤ 2N` (the order form).
* `Spider.exbip_le` — the fixed-part form `ex_bip(m, n; T) ≤ 2(m + n)`: a `T`-free graph on
  `Fin m ⊕ Fin n` all of whose edges cross between the two summands has at most `2(m + n)` edges.
-/

open Finset SimpleGraph

namespace Spider

/-! ### The spider as a graph on `Fin 8` -/

/-- The edges of the spider: centre `0`; arms `0 — 1 — 2 — 3` and `0 — 4 — 5 — 6`; leaf `7`. -/
def spiderRel (i j : Fin 8) : Prop :=
  (i, j) ∈ [((0 : Fin 8), (1 : Fin 8)), (1, 2), (2, 3), (0, 4), (4, 5), (5, 6), (0, 7)]

instance : DecidableRel spiderRel := fun i j => by unfold spiderRel; infer_instance

/-- The spider `S(3,3,1)`: the tree obtained from the path `P₇` by attaching a leaf to its central
vertex. Vertex `0` is the centre, `0 — 1 — 2 — 3` and `0 — 4 — 5 — 6` are the two arms of length
three, and `7` is the pendant leaf. -/
def spider : SimpleGraph (Fin 8) := SimpleGraph.fromRel spiderRel

instance : DecidableRel spider.Adj := by unfold spider; infer_instance

/-- Sanity check: the spider has eight vertices and seven edges. -/
example : #spider.edgeFinset = 7 := by decide

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An explicit spider centred at `v` yields a copy of `spider` in `G` in Mathlib's sense. -/
theorem isContained_of_hasSpiderAt {v : V} (h : HasSpiderAt G v) : spider ⊑ G := by
  obtain ⟨x₁, y₁, z₁, x₂, y₂, z₂, x₄, hnd, h1, h2, h3, h4, h5, h6, h7⟩ := h
  let f : Fin 8 → V := ![v, x₁, y₁, z₁, x₂, y₂, z₂, x₄]
  have hf : Function.Injective f := by
    rw [← List.nodup_ofFn]
    simpa [f, List.ofFn_succ] using hnd
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd hij (by decide)
    | exact h1 | exact h1.symm | exact h2 | exact h2.symm | exact h3 | exact h3.symm
    | exact h4 | exact h4.symm | exact h5 | exact h5.symm | exact h6 | exact h6.symm
    | exact h7 | exact h7.symm

/-! ### The main theorem, restated -/

/-- **Theorem 1.1 (containment form).** Every bipartite graph `G` (given by a proper 2-colouring
`c`) with `e(G) > 2·v(G)` contains a copy of the spider `S(3,3,1)`. -/
theorem spider_isContained (c : V → Bool) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (h : 2 * Fintype.card V < #G.edgeFinset) : spider ⊑ G := by
  obtain ⟨v, hv⟩ := main c hc h
  exact isContained_of_hasSpiderAt hv

/-- **Theorem 1.1 (order form, `ex_bip(N; T) ≤ 2N`).** A spider-free bipartite graph on `N`
vertices has at most `2N` edges. -/
theorem edge_bound (c : V → Bool) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (hfree : spider.Free G) : #G.edgeFinset ≤ 2 * Fintype.card V := by
  by_contra h
  exact hfree (spider_isContained c hc (by omega))

/-- The same bound with bipartiteness expressed as Mathlib's `G.Colorable 2`. -/
theorem edge_bound_of_colorable (hcol : G.Colorable 2) (hfree : spider.Free G) :
    #G.edgeFinset ≤ 2 * Fintype.card V := by
  obtain ⟨C⟩ := hcol
  refine edge_bound (fun v => decide (C v = 0)) ?_ hfree
  intro u w huw
  have hne : C u ≠ C w := C.valid huw
  revert hne
  generalize C u = a
  generalize C w = b
  revert a b
  decide

/-- **Theorem 1.1 (fixed-part form, `ex_bip(m, n; T) ≤ 2(m + n)`).** A spider-free bipartite
graph with parts `Fin m` and `Fin n` — a graph on `Fin m ⊕ Fin n` every edge of which joins the two
summands — has at most `2(m + n)` edges. -/
theorem exbip_le (m n : ℕ) (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj]
    (hcross : ∀ a b, G.Adj a b → a.isLeft ≠ b.isLeft) (hfree : spider.Free G) :
    #G.edgeFinset ≤ 2 * (m + n) := by
  have := edge_bound (G := G) Sum.isLeft hcross hfree
  simpa using this

end Spider

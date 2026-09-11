import Spider.Extremal

/-!
# Sharpness (Remark 4.2 and Proposition 6.1, first part)

* `Spider.spider_free_K44` — Remark 4.2: `K₄,₄` contains no spider, although it has minimum
  degree `4`.
* `Spider.exbip_four_four` — the case `q = 1` of Proposition 6.1: `ex_bip(4, 4; T) = 16`.
* `Spider.spider_free_qK44`, `Spider.card_edgeFinset_qK44`, `Spider.exbip_eq_of_qK44` —
  Proposition 6.1 in the order form: for every `q`, the disjoint union `q·K₄,₄` (realised as the
  box product `⊥ □ K₄,₄` on `Fin q × (Fin 4 ⊕ Fin 4)`) is a spider-free bipartite graph on `8q`
  vertices with exactly `16q = 2·(8q)` edges, whose two colour classes have `4q` vertices each. So
  the bound `ex_bip(N; T) ≤ 2N` of Theorem 1.1 is attained for every `N = 8q`.
-/

open Finset SimpleGraph

namespace Spider

/-- If `a ≠ b` in `Bool`, then `a = !b`. -/
lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := Bool.eq_not_of_ne h

/-! ### `K₄,₄` -/

/-- The complete bipartite graph `K₄,₄`. -/
abbrev K44 : SimpleGraph (Fin 4 ⊕ Fin 4) := completeBipartiteGraph (Fin 4) (Fin 4)

instance : DecidableRel K44.Adj := fun a b =>
  inferInstanceAs (Decidable (a.isLeft ∧ b.isRight ∨ a.isRight ∧ b.isLeft))

lemma K44_adj_isLeft : ∀ a b : Fin 4 ⊕ Fin 4, K44.Adj a b → a.isLeft ≠ b.isLeft := by decide

lemma K44_card_edgeFinset : #K44.edgeFinset = 16 := by decide

lemma K44_degree : ∀ a : Fin 4 ⊕ Fin 4, K44.degree a = 4 := by decide

/-- In any copy of the spider inside a bipartite graph, the five vertices `1, 3, 4, 6, 7` (those at
odd distance from the centre) all lie in the colour class opposite to the centre. -/
lemma odd_vertices_isLeft {W : Type*} (H : SimpleGraph W) (c : W → Bool)
    (hc : ∀ u w, H.Adj u w → c u ≠ c w) (f : spider.Copy H) :
    ∀ i ∈ ({1, 3, 4, 6, 7} : Finset (Fin 8)), c (f i) = !c (f 0) := by
  have hadj : ∀ i j, spider.Adj i j → c (f i) ≠ c (f j) := fun i j h => hc _ _ (f.toHom.map_rel h)
  have h01 := hadj 0 1 (by decide)
  have h12 := hadj 1 2 (by decide)
  have h23 := hadj 2 3 (by decide)
  have h04 := hadj 0 4 (by decide)
  have h45 := hadj 4 5 (by decide)
  have h56 := hadj 5 6 (by decide)
  have h07 := hadj 0 7 (by decide)
  have e1 : c (f 1) = !c (f 0) := bool_eq_not_of_ne h01.symm
  have e2 : c (f 2) = c (f 0) := bool_eq_of_ne_of_ne h01.symm h12
  have e3 : c (f 3) = !c (f 0) := by rw [← e2]; exact bool_eq_not_of_ne h23.symm
  have e4 : c (f 4) = !c (f 0) := bool_eq_not_of_ne h04.symm
  have e5 : c (f 5) = c (f 0) := bool_eq_of_ne_of_ne h04.symm h45
  have e6 : c (f 6) = !c (f 0) := by rw [← e5]; exact bool_eq_not_of_ne h56.symm
  have e7 : c (f 7) = !c (f 0) := bool_eq_not_of_ne h07.symm
  intro i hi
  simp only [mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- **Remark 4.2.** `K₄,₄` has minimum degree `4` but contains no spider: the larger colour class
of the spider has five vertices, whereas each side of `K₄,₄` has four. -/
theorem spider_free_K44 : spider.Free K44 := by
  rintro ⟨f⟩
  have hodd := odd_vertices_isLeft K44 Sum.isLeft K44_adj_isLeft f
  have hsub : ({1, 3, 4, 6, 7} : Finset (Fin 8)).image f
      ⊆ univ.filter (fun x : Fin 4 ⊕ Fin 4 => x.isLeft = !(f 0).isLeft) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    exact mem_filter.2 ⟨mem_univ _, hodd i hi⟩
  have hinj : Function.Injective (⇑f) := f.injective
  have h5 : #(({1, 3, 4, 6, 7} : Finset (Fin 8)).image f) = 5 := by
    rw [card_image_of_injective _ hinj]; rfl
  have h4 : #(univ.filter (fun x : Fin 4 ⊕ Fin 4 => x.isLeft = !(f 0).isLeft)) = 4 := by
    generalize (f 0).isLeft = b
    cases b <;> decide
  have := card_le_card hsub
  omega

/-- **Proposition 6.1 for `q = 1`: `ex_bip(4, 4; T) = 16`.** `K₄,₄` is a spider-free bipartite
graph with parts of size `4` and `16` edges, and no such graph has more. -/
theorem exbip_four_four :
    (∀ a b, K44.Adj a b → a.isLeft ≠ b.isLeft) ∧ spider.Free K44 ∧ #K44.edgeFinset = 16 ∧
    ∀ (G : SimpleGraph (Fin 4 ⊕ Fin 4)) [DecidableRel G.Adj],
      (∀ a b, G.Adj a b → a.isLeft ≠ b.isLeft) → spider.Free G → #G.edgeFinset ≤ 16 :=
  ⟨K44_adj_isLeft, spider_free_K44, K44_card_edgeFinset,
    fun G _ hcross hfree => exbip_le 4 4 G hcross hfree⟩

/-! ### `q` disjoint copies of `K₄,₄` -/

/-- `q` disjoint copies of `K₄,₄`, realised as the box product `⊥ □ K₄,₄` on
`Fin q × (Fin 4 ⊕ Fin 4)`: `(i, a) ~ (j, b)` iff `i = j` and `a ~ b` in `K₄,₄`. -/
abbrev qK44 (q : ℕ) : SimpleGraph (Fin q × (Fin 4 ⊕ Fin 4)) := (⊥ : SimpleGraph (Fin q)) □ K44

instance (q : ℕ) : DecidableRel (qK44 q).Adj := fun x y =>
  inferInstanceAs (Decidable ((⊥ : SimpleGraph (Fin q)).Adj x.1 y.1 ∧ x.2 = y.2 ∨
    K44.Adj x.2 y.2 ∧ x.1 = y.1))

lemma qK44_adj {q : ℕ} {x y : Fin q × (Fin 4 ⊕ Fin 4)} :
    (qK44 q).Adj x y ↔ K44.Adj x.2 y.2 ∧ x.1 = y.1 := by
  simp [qK44, boxProd_adj]

/-- `q·K₄,₄` is bipartite, coloured by the side of the `K₄,₄`-coordinate. -/
lemma qK44_adj_isLeft (q : ℕ) : ∀ x y, (qK44 q).Adj x y → x.2.isLeft ≠ y.2.isLeft :=
  fun _ _ h => K44_adj_isLeft _ _ (qK44_adj.1 h).1

/-- Each colour class of `q·K₄,₄` has `4q` vertices. -/
lemma qK44_card_side (q : ℕ) (b : Bool) :
    #(univ.filter (fun x : Fin q × (Fin 4 ⊕ Fin 4) => x.2.isLeft = b)) = 4 * q := by
  let emb : Fin q × Fin 4 ↪ Fin q × (Fin 4 ⊕ Fin 4) :=
    ⟨fun p => (p.1, if b then Sum.inl p.2 else Sum.inr p.2), by
      rintro ⟨i, a⟩ ⟨j, a'⟩ h
      cases b <;> simp_all⟩
  have hside : univ.filter (fun x : Fin q × (Fin 4 ⊕ Fin 4) => x.2.isLeft = b)
      = (univ : Finset (Fin q × Fin 4)).map emb := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_map, emb]
    constructor
    · intro hx
      obtain ⟨i, a⟩ := x
      rcases a with a | a
      · cases b
        · simp at hx
        · exact ⟨(i, a), rfl⟩
      · cases b
        · exact ⟨(i, a), rfl⟩
        · simp at hx
    · rintro ⟨⟨i, a⟩, rfl⟩
      cases b <;> rfl
  rw [hside, card_map, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

/-- **Proposition 6.1 (spider-freeness).** `q·K₄,₄` contains no spider: a copy of the connected
spider lies inside one component, i.e. inside one copy of `K₄,₄`. -/
theorem spider_free_qK44 (q : ℕ) : spider.Free (qK44 q) := by
  rintro ⟨f⟩
  apply spider_free_K44
  have hadj : ∀ i j, spider.Adj i j → K44.Adj (f i).2 (f j).2 ∧ (f i).1 = (f j).1 :=
    fun i j h => qK44_adj.1 (f.toHom.map_rel h)
  have h01 := (hadj 0 1 (by decide)).2
  have h12 := (hadj 1 2 (by decide)).2
  have h23 := (hadj 2 3 (by decide)).2
  have h04 := (hadj 0 4 (by decide)).2
  have h45 := (hadj 4 5 (by decide)).2
  have h56 := (hadj 5 6 (by decide)).2
  have h07 := (hadj 0 7 (by decide)).2
  have hfst : ∀ i, (f i).1 = (f 0).1 := by
    intro i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact (h12.symm.trans h01.symm)
    · exact (h23.symm.trans (h12.symm.trans h01.symm))
    · exact h04.symm
    · exact (h45.symm.trans h04.symm)
    · exact (h56.symm.trans (h45.symm.trans h04.symm))
    · exact h07.symm
  refine ⟨⟨⟨fun i => (f i).2, fun {i j} h => (hadj i j h).1⟩, ?_⟩⟩
  intro i j hij
  apply f.injective
  exact Prod.ext ((hfst i).trans (hfst j).symm) hij

/-- **Proposition 6.1 (edge count).** `q·K₄,₄` has exactly `16q` edges. -/
theorem card_edgeFinset_qK44 (q : ℕ) : #(qK44 q).edgeFinset = 16 * q := by
  have hdeg : ∀ x : Fin q × (Fin 4 ⊕ Fin 4), (qK44 q).degree x = 4 := by
    intro x
    rw [degree_boxProd, bot_degree, K44_degree, zero_add]
  have hsum := (qK44 q).sum_degrees_eq_twice_card_edges
  rw [sum_const_nat (m := 4) (fun x _ => ?_), card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_sum, Fintype.card_fin] at hsum
  · omega
  · -- the `Fintype` instances on the neighbour set differ syntactically but are subsingletons
    convert hdeg x

/-- **Proposition 6.1 (order form): the bound of Theorem 1.1 is attained for every `N = 8q`.**
`q·K₄,₄` is a spider-free bipartite graph on `8q` vertices, with `4q` vertices in each colour class
and exactly `16q = 2·(8q)` edges; by Theorem 1.1 no spider-free bipartite graph on `8q` vertices
has more edges. -/
theorem exbip_eq_of_qK44 (q : ℕ) :
    Fintype.card (Fin q × (Fin 4 ⊕ Fin 4)) = 8 * q ∧
    (∀ x y, (qK44 q).Adj x y → x.2.isLeft ≠ y.2.isLeft) ∧
    (∀ b, #(univ.filter (fun x : Fin q × (Fin 4 ⊕ Fin 4) => x.2.isLeft = b)) = 4 * q) ∧
    spider.Free (qK44 q) ∧
    #(qK44 q).edgeFinset = 2 * Fintype.card (Fin q × (Fin 4 ⊕ Fin 4)) ∧
    ∀ (G : SimpleGraph (Fin q × (Fin 4 ⊕ Fin 4))) [DecidableRel G.Adj],
      (∀ x y, G.Adj x y → x.2.isLeft ≠ y.2.isLeft) → spider.Free G →
        #G.edgeFinset ≤ 2 * Fintype.card (Fin q × (Fin 4 ⊕ Fin 4)) := by
  have hcard : Fintype.card (Fin q × (Fin 4 ⊕ Fin 4)) = 8 * q := by simp; ring
  refine ⟨hcard, qK44_adj_isLeft q, qK44_card_side q, spider_free_qK44 q, ?_, ?_⟩
  · rw [card_edgeFinset_qK44, hcard]; ring
  · intro G _ hcross hfree
    exact edge_bound (fun x => x.2.isLeft) hcross hfree

end Spider

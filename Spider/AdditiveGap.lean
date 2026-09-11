import Spider.Sharpness

/-!
# Sharpness within an additive constant (Proposition 6.1, second part)

For all part sizes `m, n ≥ 2` the paper constructs a spider-free bipartite graph with parts of
sizes `m` and `n` and `2(m + n) - 8` edges: split `U = U₁ ∪ U₂`, `W = W₁ ∪ W₂` with
`|U₁| = |W₂| = 2`, `|U₂| = m - 2`, `|W₁| = n - 2`, and take all edges between `U₁` and `W₁` and
all edges between `U₂` and `W₂`. Every component then has a colour class of size at most `2`,
while the spider is connected with colour classes of sizes `3` and `5`.

* `Spider.gapGraph` — the construction, on `Fin m ⊕ Fin n` (`U₁, W₂` are the indices `< 2`).
* `Spider.spider_free_gapGraph` — it is spider-free.
* `Spider.card_edgeFinset_gapGraph` — it has exactly `2(m + n) - 8` edges.
* `Spider.exbip_within_eight` — together with Theorem 1.1: `2(m+n) - 8 ≤ ex_bip(m,n;T) ≤ 2(m+n)`.
-/

open Finset SimpleGraph

namespace Spider

/-! ### The construction -/

/-- Whether a vertex of `Fin m ⊕ Fin n` has index `< 2`, i.e. lies in `U₁` or `W₂`. -/
def small {m n : ℕ} : Fin m ⊕ Fin n → Bool
  | Sum.inl i => decide (i.val < 2)
  | Sum.inr j => decide (j.val < 2)

/-- `inl i ~ inr j` iff `(i ∈ U₁ ∧ j ∈ W₁) ∨ (i ∈ U₂ ∧ j ∈ W₂)`. -/
def gapRel (m n : ℕ) : Fin m ⊕ Fin n → Fin m ⊕ Fin n → Prop
  | Sum.inl i, Sum.inr j => (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2)
  | _, _ => False

instance (m n : ℕ) : DecidableRel (gapRel m n) := fun a b => by
  cases a <;> cases b <;> simp only [gapRel] <;> infer_instance

/-- The extremal construction of Proposition 6.1: the disjoint union of `K_{2, n-2}` and
`K_{m-2, 2}` on the parts `Fin m` and `Fin n`. -/
def gapGraph (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) := SimpleGraph.fromRel (gapRel m n)

instance (m n : ℕ) : DecidableRel (gapGraph m n).Adj := by unfold gapGraph; infer_instance

lemma gapGraph_adj_inl_inr {m n : ℕ} (i : Fin m) (j : Fin n) :
    (gapGraph m n).Adj (Sum.inl i) (Sum.inr j) ↔
      (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2) := by
  simp [gapGraph, fromRel_adj, gapRel]

lemma gapGraph_adj_inr_inl {m n : ℕ} (i : Fin m) (j : Fin n) :
    (gapGraph m n).Adj (Sum.inr j) (Sum.inl i) ↔
      (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2) := by
  rw [adj_comm, gapGraph_adj_inl_inr]

lemma gapGraph_not_adj_inl_inl {m n : ℕ} (i i' : Fin m) :
    ¬ (gapGraph m n).Adj (Sum.inl i) (Sum.inl i') := by
  simp [gapGraph, fromRel_adj, gapRel]

lemma gapGraph_not_adj_inr_inr {m n : ℕ} (j j' : Fin n) :
    ¬ (gapGraph m n).Adj (Sum.inr j) (Sum.inr j') := by
  simp [gapGraph, fromRel_adj, gapRel]

/-- The construction is bipartite with parts `Fin m` and `Fin n`. -/
lemma gapGraph_isLeft {m n : ℕ} : ∀ a b, (gapGraph m n).Adj a b → a.isLeft ≠ b.isLeft := by
  intro a b h
  rcases a with i | j <;> rcases b with i' | j'
  · exact absurd h (gapGraph_not_adj_inl_inl _ _)
  · simp
  · simp
  · exact absurd h (gapGraph_not_adj_inr_inr _ _)

/-- Adjacent vertices differ in `small` as well: every edge joins an index `< 2` to an index
`≥ 2`. -/
lemma gapGraph_small {m n : ℕ} : ∀ a b, (gapGraph m n).Adj a b → small a ≠ small b := by
  intro a b h
  rcases a with i | j <;> rcases b with i' | j'
  · exact absurd h (gapGraph_not_adj_inl_inl _ _)
  · rw [gapGraph_adj_inl_inr] at h
    simp only [small]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : ¬ j'.val < 2 := by omega
      simp [h1, this]
    · have : ¬ i.val < 2 := by omega
      simp [h2, this]
  · rw [gapGraph_adj_inr_inl] at h
    simp only [small]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : ¬ j.val < 2 := by omega
      simp [h1, this]
    · have : ¬ i'.val < 2 := by omega
      simp [h2, this]
  · exact absurd h (gapGraph_not_adj_inr_inr _ _)

/-! ### Spider-freeness -/

/-- In any copy of the spider inside a bipartite graph, the vertices `0, 2, 5` (those at even
distance from the centre) lie in the colour class of the centre. -/
lemma even_vertices {W : Type*} (H : SimpleGraph W) (c : W → Bool)
    (hc : ∀ u w, H.Adj u w → c u ≠ c w) (f : spider.Copy H) :
    ∀ i ∈ ({0, 2, 5} : Finset (Fin 8)), c (f i) = c (f 0) := by
  have hadj : ∀ i j, spider.Adj i j → c (f i) ≠ c (f j) := fun i j h => hc _ _ (f.toHom.map_rel h)
  have h01 := hadj 0 1 (by decide)
  have h12 := hadj 1 2 (by decide)
  have h04 := hadj 0 4 (by decide)
  have h45 := hadj 4 5 (by decide)
  have e2 : c (f 2) = c (f 0) := bool_eq_of_ne_of_ne h01.symm h12
  have e5 : c (f 5) = c (f 0) := bool_eq_of_ne_of_ne h04.symm h45
  intro i hi
  simp only [mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · rfl
  · exact e2
  · exact e5

/-- Each of the two "small" classes `U₁` (left, index `< 2`) and `W₂` (right, index `< 2`) has at
most two vertices. -/
lemma card_small_class_le (m n : ℕ) (b : Bool) :
    #(univ.filter (fun x : Fin m ⊕ Fin n => x.isLeft = b ∧ small x = true)) ≤ 2 := by
  rw [← card_range 2]
  refine card_le_card_of_injOn (fun x : Fin m ⊕ Fin n => x.elim Fin.val Fin.val) ?_ ?_
  · intro x hx
    rw [mem_coe, mem_filter] at hx
    rw [mem_coe, mem_range]
    obtain ⟨-, -, hS⟩ := hx
    rcases x with i | j <;> simpa [small] using hS
  · intro x hx y hy hxy
    rw [mem_coe, mem_filter] at hx hy
    obtain ⟨-, hxL, -⟩ := hx
    obtain ⟨-, hyL, -⟩ := hy
    rcases x with i | j <;> rcases y with i' | j'
    · simp only [Sum.elim_inl] at hxy
      rw [Fin.ext hxy]
    · rw [← hxL] at hyL; simp at hyL
    · rw [← hxL] at hyL; simp at hyL
    · simp only [Sum.elim_inr] at hxy
      rw [Fin.ext hxy]

/-- **Proposition 6.1 (spider-freeness of the construction).** -/
theorem spider_free_gapGraph (m n : ℕ) : spider.Free (gapGraph m n) := by
  rintro ⟨f⟩
  have hinj : Function.Injective (⇑f) := f.injective
  have hodd₁ := odd_vertices_isLeft _ Sum.isLeft gapGraph_isLeft f
  have hodd₂ := odd_vertices_isLeft _ small gapGraph_small f
  have heven₁ := even_vertices _ Sum.isLeft gapGraph_isLeft f
  have heven₂ := even_vertices _ small gapGraph_small f
  by_cases hs : small (f 0) = true
  · -- the centre is small: `f 0, f 2, f 5` are three distinct vertices in a small class
    have hsub : ({0, 2, 5} : Finset (Fin 8)).image f
        ⊆ univ.filter (fun x => x.isLeft = (f 0).isLeft ∧ small x = true) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      exact mem_filter.2 ⟨mem_univ _, heven₁ i hi, (heven₂ i hi).trans hs⟩
    have h3 : #(({0, 2, 5} : Finset (Fin 8)).image f) = 3 := by
      rw [card_image_of_injective _ hinj]; rfl
    have := card_le_card hsub
    have := card_small_class_le m n (f 0).isLeft
    omega
  · -- the centre is not small: `f 1, f 3, f 4, f 6, f 7` are five distinct vertices in a small class
    have hs' : small (f 0) = false := by simpa using hs
    have hsub : ({1, 3, 4, 6, 7} : Finset (Fin 8)).image f
        ⊆ univ.filter (fun x => x.isLeft = !(f 0).isLeft ∧ small x = true) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      refine mem_filter.2 ⟨mem_univ _, hodd₁ i hi, ?_⟩
      rw [hodd₂ i hi, hs']
      rfl
    have h5 : #(({1, 3, 4, 6, 7} : Finset (Fin 8)).image f) = 5 := by
      rw [card_image_of_injective _ hinj]; rfl
    have := card_le_card hsub
    have := card_small_class_le m n (!(f 0).isLeft)
    omega

/-! ### The edge count -/

/-- There are exactly two indices `< 2` in `Fin n` when `n ≥ 2`. -/
lemma card_filter_lt_two (n : ℕ) (hn : 2 ≤ n) :
    #(univ.filter (fun j : Fin n => j.val < 2)) = 2 := by
  have : univ.filter (fun j : Fin n => j.val < 2) = (univ : Finset (Fin 2)).map (Fin.castLEEmb hn) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    · rintro ⟨k, rfl⟩
      simp only [Fin.castLEEmb_apply, Fin.val_castLE]
      omega
  rw [this, card_map, card_univ, Fintype.card_fin]

lemma card_filter_not_lt_two (n : ℕ) (hn : 2 ≤ n) :
    #(univ.filter (fun j : Fin n => ¬ j.val < 2)) = n - 2 := by
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun j : Fin n => j.val < 2)
  rw [card_filter_lt_two n hn, card_univ, Fintype.card_fin] at this
  omega

lemma neighborFinset_inl (m n : ℕ) (i : Fin m) :
    (gapGraph m n).neighborFinset (Sum.inl i) =
      (univ.filter (fun j : Fin n => (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2))).map
        Function.Embedding.inr := by
  ext x
  rcases x with i' | j
  · simp [gapGraph_not_adj_inl_inl]
  · simp [gapGraph_adj_inl_inr]

lemma neighborFinset_inr (m n : ℕ) (j : Fin n) :
    (gapGraph m n).neighborFinset (Sum.inr j) =
      (univ.filter (fun i : Fin m => (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2))).map
        Function.Embedding.inl := by
  ext x
  rcases x with i | j'
  · simp [gapGraph_adj_inr_inl]
  · simp [gapGraph_not_adj_inr_inr]

lemma degree_inl (m n : ℕ) (hn : 2 ≤ n) (i : Fin m) :
    (gapGraph m n).degree (Sum.inl i) = if i.val < 2 then n - 2 else 2 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_inl, card_map]
  split_ifs with hi
  · have : (univ.filter (fun j : Fin n => (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2)))
        = univ.filter (fun j : Fin n => ¬ j.val < 2) := by
      ext j; simp only [mem_filter, mem_univ, true_and]; omega
    rw [this, card_filter_not_lt_two n hn]
  · have : (univ.filter (fun j : Fin n => (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2)))
        = univ.filter (fun j : Fin n => j.val < 2) := by
      ext j; simp only [mem_filter, mem_univ, true_and]; omega
    rw [this, card_filter_lt_two n hn]

lemma degree_inr (m n : ℕ) (hm : 2 ≤ m) (j : Fin n) :
    (gapGraph m n).degree (Sum.inr j) = if j.val < 2 then m - 2 else 2 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_inr, card_map]
  split_ifs with hj
  · have : (univ.filter (fun i : Fin m => (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2)))
        = univ.filter (fun i : Fin m => ¬ i.val < 2) := by
      ext i; simp only [mem_filter, mem_univ, true_and]; omega
    rw [this, card_filter_not_lt_two m hm]
  · have : (univ.filter (fun i : Fin m => (i.val < 2 ∧ 2 ≤ j.val) ∨ (2 ≤ i.val ∧ j.val < 2)))
        = univ.filter (fun i : Fin m => i.val < 2) := by
      ext i; simp only [mem_filter, mem_univ, true_and]; omega
    rw [this, card_filter_lt_two m hm]

/-- **Proposition 6.1 (edge count of the construction).** -/
theorem card_edgeFinset_gapGraph (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    #(gapGraph m n).edgeFinset = 2 * (m + n) - 8 := by
  have hsum := (gapGraph m n).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at hsum
  have hL : ∑ i : Fin m, (gapGraph m n).degree (Sum.inl i) = 2 * (n - 2) + (m - 2) * 2 := by
    rw [sum_congr rfl (fun i _ => degree_inl m n hn i), sum_ite, sum_const, sum_const,
      smul_eq_mul, smul_eq_mul, card_filter_lt_two m hm, card_filter_not_lt_two m hm]
  have hR : ∑ j : Fin n, (gapGraph m n).degree (Sum.inr j) = 2 * (m - 2) + (n - 2) * 2 := by
    rw [sum_congr rfl (fun j _ => degree_inr m n hm j), sum_ite, sum_const, sum_const,
      smul_eq_mul, smul_eq_mul, card_filter_lt_two n hn, card_filter_not_lt_two n hn]
  rw [hL, hR] at hsum
  omega

/-- **Proposition 6.1, second part: `ex_bip(m, n; T) ≥ 2(m + n) - 8` for `m, n ≥ 2`.** -/
theorem exbip_ge (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∀ a b, (gapGraph m n).Adj a b → a.isLeft ≠ b.isLeft) ∧ spider.Free (gapGraph m n) ∧
      #(gapGraph m n).edgeFinset = 2 * (m + n) - 8 :=
  ⟨gapGraph_isLeft, spider_free_gapGraph m n, card_edgeFinset_gapGraph m n hm hn⟩

/-- **Sharpness within an additive constant of `8`.** For all `m, n ≥ 2`, some spider-free
bipartite graph with parts `Fin m`, `Fin n` has `2(m + n) - 8` edges (`exbip_ge`), and none has
more than `2(m + n)` (`exbip_le`). -/
theorem exbip_within_eight (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∃ (G : SimpleGraph (Fin m ⊕ Fin n)) (_ : DecidableRel G.Adj),
      (∀ a b, G.Adj a b → a.isLeft ≠ b.isLeft) ∧ spider.Free G ∧
        #G.edgeFinset = 2 * (m + n) - 8) ∧
    ∀ (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj],
      (∀ a b, G.Adj a b → a.isLeft ≠ b.isLeft) → spider.Free G → #G.edgeFinset ≤ 2 * (m + n) :=
  ⟨⟨gapGraph m n, inferInstance, exbip_ge m n hm hn⟩, fun G _ hcross hfree => exbip_le m n G hcross hfree⟩

end Spider

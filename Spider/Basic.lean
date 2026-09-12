import Mathlib

/-!
# A fixed-part bipartite extremal bound for the eight-vertex spider

Formalisation of the main theorem of

> Peter Lowes, *A fixed-part bipartite extremal bound for the eight-vertex spider*,
> Zenodo, version 1.0, 3 August 2026, doi:10.5281/zenodo.21783225.

Let `T = S(3,3,1)` be the spider with two arms of length three and one arm of length one,
i.e. the tree obtained from the seven-vertex path `P₇` by attaching a leaf to its central vertex.
The paper proves that every bipartite graph `G` with `e(G) > 2·v(G)` contains a copy of `T`, so
that `ex_bip(m, n; T) ≤ 2(m + n)` for all part sizes `m, n`.

The Lean development follows the paper's three steps:

* `Spider.core` — the 3-core reduction (Lemma 3.1): a vertex set with more than twice as many
  internal edges as vertices contains a nonempty subset in which every vertex has at least three
  neighbours inside the subset, still with the same density property.
* `Spider.exists_five_nbr` — the averaging step (equation (3.2)): in a bipartite such subset, some
  vertex of the smaller colour class has at least five neighbours inside the subset.
* `Spider.hasSpiderAt_of_three_five` — the rooted embedding lemma (Lemma 4.1).

The main results are `Spider.main`, `Spider.spider_isContained`, `Spider.edge_bound`,
`Spider.edge_bound_of_colorable` and the fixed-part form `Spider.exbip_le`.
-/

open Finset SimpleGraph

namespace Spider

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Neighbourhoods inside a vertex set and the degree sum -/

/-- The neighbours of `x` that lie inside the vertex set `S`. -/
def nbr (S : Finset V) (x : V) : Finset V := G.neighborFinset x ∩ S

/-- Twice the number of edges of `G` with both endpoints in `S`: the sum, over `x ∈ S`, of the
number of neighbours of `x` inside `S`. -/
def dsum (S : Finset V) : ℕ := ∑ x ∈ S, #(nbr G S x)

variable {G}

@[simp] lemma mem_nbr {S : Finset V} {x y : V} : y ∈ nbr G S x ↔ G.Adj x y ∧ y ∈ S := by
  simp [nbr]

lemma mem_of_mem_nbr {S : Finset V} {x y : V} (h : y ∈ nbr G S x) : y ∈ S := (mem_nbr.1 h).2

lemma adj_of_mem_nbr {S : Finset V} {x y : V} (h : y ∈ nbr G S x) : G.Adj x y := (mem_nbr.1 h).1

lemma nbr_symm {S : Finset V} {x y : V} (hx : x ∈ S) (h : y ∈ nbr G S x) : x ∈ nbr G S y :=
  mem_nbr.2 ⟨(adj_of_mem_nbr h).symm, hx⟩

lemma nbr_univ (x : V) : nbr G univ x = G.neighborFinset x := by simp [nbr]

lemma nbr_erase {S : Finset V} {x y : V} :
    nbr G (S.erase x) y = (nbr G S y).erase x := by
  simp [nbr, inter_erase]

/-- Removing a vertex `x` from `S` changes the number of neighbours of `y ≠ x` inside `S` by one
exactly when `y` is adjacent to `x`. -/
lemma card_nbr_erase {S : Finset V} {x y : V} (hx : x ∈ S) :
    #(nbr G S y) = #(nbr G (S.erase x) y) + if G.Adj y x then 1 else 0 := by
  rw [nbr_erase]
  by_cases h : G.Adj y x
  · have hmem : x ∈ nbr G S y := mem_nbr.2 ⟨h, hx⟩
    rw [if_pos h, card_erase_add_one hmem]
  · have hmem : x ∉ nbr G S y := fun hm => h (adj_of_mem_nbr hm)
    rw [if_neg h, erase_eq_of_notMem hmem, add_zero]

/-- Deleting a vertex of degree `d` (inside `S`) removes exactly `d` edges, i.e. lowers the degree
sum by `2d`. This is equation (3.1) of the paper. -/
lemma dsum_erase {S : Finset V} {x : V} (hx : x ∈ S) :
    dsum G S = dsum G (S.erase x) + 2 * #(nbr G S x) := by
  unfold dsum
  rw [← sum_erase_add S _ hx]
  have h1 : ∑ y ∈ S.erase x, #(nbr G S y)
      = ∑ y ∈ S.erase x, (#(nbr G (S.erase x) y) + if G.Adj y x then 1 else 0) := by
    refine sum_congr rfl fun y _ => ?_
    exact card_nbr_erase hx
  have h2 : (∑ y ∈ S.erase x, if G.Adj y x then 1 else 0) = #(nbr G S x) := by
    rw [sum_boole, Nat.cast_id]
    congr 1
    ext y
    simp only [mem_filter, mem_erase, mem_nbr]
    constructor
    · rintro ⟨⟨-, hyS⟩, hadj⟩
      exact ⟨hadj.symm, hyS⟩
    · rintro ⟨hadj, hyS⟩
      exact ⟨⟨hadj.ne.symm, hyS⟩, hadj.symm⟩
  rw [h1, sum_add_distrib, h2]
  ring

/-! ### The 3-core reduction (Lemma 3.1) -/

/-- **3-core reduction.** If `S` spans more than `2·|S|` edges, then `S` contains a nonempty subset
`H` spanning more than `2·|H|` edges in which every vertex has at least three neighbours inside
`H`. -/
theorem core (S : Finset V) (hS : 4 * #S < dsum G S) :
    ∃ H ⊆ S, H.Nonempty ∧ 4 * #H < dsum G H ∧ ∀ x ∈ H, 3 ≤ #(nbr G H x) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hx : ∃ x ∈ S, #(nbr G S x) ≤ 2
    · obtain ⟨x, hxS, hd⟩ := hx
      have h1 := dsum_erase (G := G) hxS
      have h2 := card_erase_add_one hxS
      obtain ⟨H, hHS, hne, hH, hdeg⟩ := ih (S.erase x) (erase_ssubset hxS) (by omega)
      exact ⟨H, hHS.trans (erase_subset x S), hne, hH, hdeg⟩
    · push Not at hx
      refine ⟨S, subset_rfl, ?_, hS, fun x hx' => hx x hx'⟩
      rw [nonempty_iff_ne_empty]
      rintro rfl
      simp [dsum] at hS

/-! ### The averaging step (equation (3.2)) -/

/-- If `a ≠ b` and `a ≠ d` in `Bool`, then `d = b`. -/
lemma bool_eq_of_ne_of_ne {a b d : Bool} (h1 : a ≠ b) (h2 : a ≠ d) : d = b := by
  revert a b d; decide

/-- Double counting the edges between the two colour classes of a bipartite vertex set `H`. -/
lemma sum_nbr_side_eq (H : Finset V) (c : V → Bool) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (b : Bool) :
    ∑ x ∈ H.filter (fun x => ¬ c x = b), #(nbr G H x)
      = ∑ y ∈ H.filter (fun x => c x = b), #(nbr G H y) := by
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
    (s := H.filter (fun x => ¬ c x = b)) (t := H.filter (fun x => c x = b))
  have hL : ∀ x ∈ H.filter (fun x => ¬ c x = b),
      #(nbr G H x) = #((H.filter (fun x => c x = b)).bipartiteAbove G.Adj x) := by
    intro x hx
    rw [mem_filter] at hx
    congr 1
    ext y
    simp only [mem_nbr, mem_bipartiteAbove, mem_filter]
    constructor
    · rintro ⟨hadj, hyH⟩
      exact ⟨⟨hyH, bool_eq_of_ne_of_ne hx.2 (hc _ _ hadj)⟩, hadj⟩
    · rintro ⟨⟨hyH, -⟩, hadj⟩
      exact ⟨hadj, hyH⟩
  have hR : ∀ y ∈ H.filter (fun x => c x = b),
      #(nbr G H y) = #((H.filter (fun x => ¬ c x = b)).bipartiteBelow G.Adj y) := by
    intro y hy
    rw [mem_filter] at hy
    congr 1
    ext x
    simp only [mem_nbr, mem_bipartiteBelow, mem_filter]
    constructor
    · rintro ⟨hadj, hxH⟩
      refine ⟨⟨hxH, ?_⟩, hadj.symm⟩
      rw [← hy.2]
      exact (hc _ _ hadj).symm
    · rintro ⟨⟨hxH, -⟩, hadj⟩
      exact ⟨hadj.symm, hxH⟩
  rw [sum_congr rfl hL, sum_congr rfl hR]
  exact key

/-- The averaging step for the colour class `b`, assuming it is the smaller class. -/
lemma exists_five_nbr_side (H : Finset V) (c : V → Bool) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (hH : 4 * #H < dsum G H) (b : Bool)
    (hb : #(H.filter (fun x => c x = b)) ≤ #(H.filter (fun x => ¬ c x = b))) :
    ∃ v ∈ H, 5 ≤ #(nbr G H v) := by
  have hsplit := card_filter_add_card_filter_not (s := H) (fun x => c x = b)
  have hsum := sum_filter_add_sum_filter_not H (fun x => c x = b) (fun x => #(nbr G H x))
  have hdc := sum_nbr_side_eq H c hc b
  have hY : ∑ y ∈ H.filter (fun x => c x = b), 4 < ∑ y ∈ H.filter (fun x => c x = b), #(nbr G H y) := by
    rw [sum_const, smul_eq_mul]
    unfold dsum at hH
    omega
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_sum_lt hY
  exact ⟨v, (mem_filter.1 hv).1, hlt⟩

/-- **Averaging step.** In a bipartite vertex set `H` spanning more than `2·|H|` edges, some vertex
has at least five neighbours inside `H`. (The paper takes it in the smaller colour class.) -/
theorem exists_five_nbr (H : Finset V) (c : V → Bool) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (hH : 4 * #H < dsum G H) : ∃ v ∈ H, 5 ≤ #(nbr G H v) := by
  by_cases hb : #(H.filter (fun x => c x = true)) ≤ #(H.filter (fun x => ¬ c x = true))
  · exact exists_five_nbr_side H c hc hH true hb
  · refine exists_five_nbr_side H c hc hH false ?_
    push Not at hb
    simpa [Bool.not_eq_true, Bool.not_eq_false] using hb.le

/-! ### The spider -/

/-- `G` contains a copy of the spider `S(3,3,1)` centred at `v`: two arms `v — x₁ — y₁ — z₁` and
`v — x₂ — y₂ — z₂` of length three and a pendant edge `v — x₄`, on eight distinct vertices. The
copy need not be induced. -/
def HasSpiderAt (G : SimpleGraph V) (v : V) : Prop :=
  ∃ x₁ y₁ z₁ x₂ y₂ z₂ x₄ : V,
    [v, x₁, y₁, z₁, x₂, y₂, z₂, x₄].Nodup ∧
    G.Adj v x₁ ∧ G.Adj x₁ y₁ ∧ G.Adj y₁ z₁ ∧
    G.Adj v x₂ ∧ G.Adj x₂ y₂ ∧ G.Adj y₂ z₂ ∧
    G.Adj v x₄

/-! ### Distinct representatives -/

omit [Fintype V] in
/-- Two nonempty finite sets whose union has at least two elements admit distinct
representatives. -/
lemma exists_ne_of_two_le_card_union {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : 2 ≤ #(A ∪ B)) : ∃ a ∈ A, ∃ b ∈ B, a ≠ b := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  by_cases hab : a = b
  · subst hab
    obtain ⟨p, hp, hpa⟩ := exists_mem_ne (s := A ∪ B) (by omega) a
    rcases mem_union.1 hp with hpA | hpB
    · exact ⟨p, hpA, a, hb, hpa⟩
    · exact ⟨a, ha, p, hpB, hpa.symm⟩
  · exact ⟨a, ha, b, hb, hab⟩

omit [Fintype V] in
/-- A set with at least two elements and a nonempty set admit distinct representatives. -/
lemma exists_ne_of_two_le_card {A B : Finset V} (hA : 2 ≤ #A) (hB : B.Nonempty) :
    ∃ a ∈ A, ∃ b ∈ B, a ≠ b :=
  exists_ne_of_two_le_card_union (card_pos.1 (by omega)) hB
    (hA.trans (card_le_card subset_union_left))

/-! ### The rooted embedding lemma (Lemma 4.1) -/

/-- Assembling the spider from a seven-vertex path `z₁ — y₁ — x₁ — v — x₂ — y₂ — z₂` centred at
`v` together with a fifth neighbour of `v`. Bipartiteness (the colouring `c`) separates the two
colour classes of the path. -/
theorem hasSpiderAt_of_path (H : Finset V) (c : V → Bool) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    {v x₁ y₁ z₁ x₂ y₂ z₂ : V} (hv : 5 ≤ #(nbr G H v))
    (hx₁ : x₁ ∈ nbr G H v) (hx₂ : x₂ ∈ nbr G H v) (hx₁₂ : x₁ ≠ x₂)
    (hy₁ : y₁ ∈ nbr G H x₁) (hy₂ : y₂ ∈ nbr G H x₂)
    (hy₁v : y₁ ≠ v) (hy₂v : y₂ ≠ v) (hy₁₂ : y₁ ≠ y₂)
    (hz₁ : z₁ ∈ nbr G H y₁) (hz₂ : z₂ ∈ nbr G H y₂)
    (hz₁x : z₁ ∉ ({x₁, x₂} : Finset V)) (hz₂x : z₂ ∉ ({x₁, x₂} : Finset V)) (hz₁₂ : z₁ ≠ z₂) :
    HasSpiderAt G v := by
  -- adjacencies
  have avx₁ : G.Adj v x₁ := adj_of_mem_nbr hx₁
  have avx₂ : G.Adj v x₂ := adj_of_mem_nbr hx₂
  have ax₁y₁ : G.Adj x₁ y₁ := adj_of_mem_nbr hy₁
  have ax₂y₂ : G.Adj x₂ y₂ := adj_of_mem_nbr hy₂
  have ay₁z₁ : G.Adj y₁ z₁ := adj_of_mem_nbr hz₁
  have ay₂z₂ : G.Adj y₂ z₂ := adj_of_mem_nbr hz₂
  -- colours: `x`'s and `z`'s have the colour opposite to `v`; `y`'s have the colour of `v`
  have cx₁ : c x₁ ≠ c v := (hc _ _ avx₁).symm
  have cx₂ : c x₂ ≠ c v := (hc _ _ avx₂).symm
  have cy₁ : c y₁ = c v := bool_eq_of_ne_of_ne cx₁ (hc _ _ ax₁y₁)
  have cy₂ : c y₂ = c v := bool_eq_of_ne_of_ne cx₂ (hc _ _ ax₂y₂)
  have cz₁ : c z₁ ≠ c v := by rw [← cy₁]; exact (hc _ _ ay₁z₁).symm
  have cz₂ : c z₂ ≠ c v := by rw [← cy₂]; exact (hc _ _ ay₂z₂).symm
  -- the pendant edge: a fifth neighbour of `v`
  obtain ⟨x₄, hx₄⟩ : (nbr G H v \ {x₁, x₂, z₁, z₂}).Nonempty := by
    apply card_pos.1
    have h1 := le_card_sdiff {x₁, x₂, z₁, z₂} (nbr G H v)
    have h2 : #({x₁, x₂, z₁, z₂} : Finset V) ≤ 4 := card_le_four
    omega
  rw [mem_sdiff] at hx₄
  have avx₄ : G.Adj v x₄ := adj_of_mem_nbr hx₄.1
  have cx₄ : c x₄ ≠ c v := (hc _ _ avx₄).symm
  simp only [mem_insert, mem_singleton, not_or] at hz₁x hz₂x hx₄
  obtain ⟨hz₁x₁, hz₁x₂⟩ := hz₁x
  obtain ⟨hz₂x₁, hz₂x₂⟩ := hz₂x
  obtain ⟨-, hx₄x₁, hx₄x₂, hx₄z₁, hx₄z₂⟩ := hx₄
  -- the twenty-eight disequalities, in list order
  have d01 : v ≠ x₁ := avx₁.ne
  have d02 : v ≠ y₁ := hy₁v.symm
  have d03 : v ≠ z₁ := fun h => cz₁ (by rw [h])
  have d04 : v ≠ x₂ := avx₂.ne
  have d05 : v ≠ y₂ := hy₂v.symm
  have d06 : v ≠ z₂ := fun h => cz₂ (by rw [h])
  have d07 : v ≠ x₄ := avx₄.ne
  have d12 : x₁ ≠ y₁ := ax₁y₁.ne
  have d13 : x₁ ≠ z₁ := fun h => hz₁x₁ h.symm
  have d14 : x₁ ≠ x₂ := hx₁₂
  have d15 : x₁ ≠ y₂ := fun h => cx₁ (by rw [h, cy₂])
  have d16 : x₁ ≠ z₂ := fun h => hz₂x₁ h.symm
  have d17 : x₁ ≠ x₄ := fun h => hx₄x₁ h.symm
  have d23 : y₁ ≠ z₁ := ay₁z₁.ne
  have d24 : y₁ ≠ x₂ := fun h => cx₂ (by rw [← h, cy₁])
  have d25 : y₁ ≠ y₂ := hy₁₂
  have d26 : y₁ ≠ z₂ := fun h => cz₂ (by rw [← h, cy₁])
  have d27 : y₁ ≠ x₄ := fun h => cx₄ (by rw [← h, cy₁])
  have d34 : z₁ ≠ x₂ := hz₁x₂
  have d35 : z₁ ≠ y₂ := fun h => cz₁ (by rw [h, cy₂])
  have d36 : z₁ ≠ z₂ := hz₁₂
  have d37 : z₁ ≠ x₄ := fun h => hx₄z₁ h.symm
  have d45 : x₂ ≠ y₂ := ax₂y₂.ne
  have d46 : x₂ ≠ z₂ := fun h => hz₂x₂ h.symm
  have d47 : x₂ ≠ x₄ := fun h => hx₄x₂ h.symm
  have d56 : y₂ ≠ z₂ := ay₂z₂.ne
  have d57 : y₂ ≠ x₄ := fun h => cx₄ (by rw [← h, cy₂])
  have d67 : z₂ ≠ x₄ := fun h => hx₄z₂ h.symm
  refine ⟨x₁, y₁, z₁, x₂, y₂, z₂, x₄, ?_, avx₁, ax₁y₁, ay₁z₁, avx₂, ax₂y₂, ay₂z₂, avx₄⟩
  simp [List.nodup_cons, d01, d02, d03, d04, d05, d06, d07, d12, d13, d14, d15, d16, d17,
    d23, d24, d25, d26, d27, d34, d35, d36, d37, d45, d46, d47, d56, d57, d67]

/-- **Rooted embedding lemma.** If every vertex of `H` has at least three neighbours inside `H`
and `v ∈ H` has at least five, then `G` contains a spider `S(3,3,1)` centred at `v`. -/
theorem hasSpiderAt_of_three_five (H : Finset V) (c : V → Bool)
    (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (hdeg : ∀ x ∈ H, 3 ≤ #(nbr G H x)) {v : V} (hv : 5 ≤ #(nbr G H v)) :
    HasSpiderAt G v := by
  -- two distinct neighbours `x₁, x₂` of `v`
  obtain ⟨x₁, hx₁, x₂, hx₂, hx₁₂⟩ := one_lt_card.1 (by omega : 1 < #(nbr G H v))
  have hx₁H : x₁ ∈ H := mem_of_mem_nbr hx₁
  have hx₂H : x₂ ∈ H := mem_of_mem_nbr hx₂
  -- distinct representatives `y₁ ∈ C₁`, `y₂ ∈ C₂` of `Cᵢ = N(xᵢ) \ {v}`, each of size `≥ 2`
  have hC₁ : 2 ≤ #((nbr G H x₁).erase v) := by
    have := pred_card_le_card_erase (s := nbr G H x₁) (a := v)
    have := hdeg x₁ hx₁H
    omega
  have hC₂ : 2 ≤ #((nbr G H x₂).erase v) := by
    have := pred_card_le_card_erase (s := nbr G H x₂) (a := v)
    have := hdeg x₂ hx₂H
    omega
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁₂⟩ :=
    exists_ne_of_two_le_card hC₁ (card_pos.1 (by omega : 0 < #((nbr G H x₂).erase v)))
  rw [mem_erase] at hy₁ hy₂
  obtain ⟨hy₁v, hy₁⟩ := hy₁
  obtain ⟨hy₂v, hy₂⟩ := hy₂
  have hy₁H : y₁ ∈ H := mem_of_mem_nbr hy₁
  have hy₂H : y₂ ∈ H := mem_of_mem_nbr hy₂
  -- the arm candidate sets `Zᵢ = N(yᵢ) \ {x₁, x₂}` (equation (4.1)), both nonempty
  have hZ₁ne : (nbr G H y₁ \ {x₁, x₂}).Nonempty := by
    apply card_pos.1
    have := le_card_sdiff {x₁, x₂} (nbr G H y₁)
    have := hdeg y₁ hy₁H
    have : #({x₁, x₂} : Finset V) ≤ 2 := card_le_two
    omega
  have hZ₂ne : (nbr G H y₂ \ {x₁, x₂}).Nonempty := by
    apply card_pos.1
    have := le_card_sdiff {x₁, x₂} (nbr G H y₂)
    have := hdeg y₂ hy₂H
    have : #({x₁, x₂} : Finset V) ≤ 2 := card_le_two
    omega
  by_cases hcase : 2 ≤ #((nbr G H y₁ \ {x₁, x₂}) ∪ (nbr G H y₂ \ {x₁, x₂}))
  · -- generic case `|Z₁ ∪ Z₂| ≥ 2`: distinct representatives `z₁ ∈ Z₁`, `z₂ ∈ Z₂`
    obtain ⟨z₁, hz₁, z₂, hz₂, hz₁₂⟩ := exists_ne_of_two_le_card_union hZ₁ne hZ₂ne hcase
    rw [mem_sdiff] at hz₁ hz₂
    exact hasSpiderAt_of_path H c hc hv hx₁ hx₂ hx₁₂ hy₁ hy₂ hy₁v hy₂v hy₁₂
      hz₁.1 hz₂.1 hz₁.2 hz₂.2 hz₁₂
  · -- the obstruction `Z₁ = Z₂ = {w}` (equation (4.2))
    push Not at hcase
    have hone := card_le_one.1 (Nat.lt_succ_iff.1 hcase)
    obtain ⟨w, hw⟩ := hZ₁ne
    obtain ⟨w', hw'⟩ := hZ₂ne
    have hww' : w = w' := hone w (mem_union_left _ hw) w' (mem_union_right _ hw')
    subst hww'
    have hwN₁ : w ∈ nbr G H y₁ := (mem_sdiff.1 hw).1
    have hwx : w ∉ ({x₁, x₂} : Finset V) := (mem_sdiff.1 hw).2
    -- `N(y₁) ⊆ {x₁, x₂, w}` and `N(y₂) ⊆ {x₁, x₂, w}`
    have hN₁ : nbr G H y₁ ⊆ {x₁, x₂, w} := by
      intro u hu
      by_cases hux : u ∈ ({x₁, x₂} : Finset V)
      · simp only [mem_insert, mem_singleton] at hux ⊢
        tauto
      · have : u = w := hone u (mem_union_left _ (mem_sdiff.2 ⟨hu, hux⟩)) w (mem_union_left _ hw)
        simp [this]
    have hN₂ : nbr G H y₂ ⊆ {x₁, x₂, w} := by
      intro u hu
      by_cases hux : u ∈ ({x₁, x₂} : Finset V)
      · simp only [mem_insert, mem_singleton] at hux ⊢
        tauto
      · have : u = w := hone u (mem_union_right _ (mem_sdiff.2 ⟨hu, hux⟩)) w (mem_union_left _ hw)
        simp [this]
    -- in fact `N(y₁) = {x₁, x₂, w}`, so `x₂ ∈ N(y₁)`
    have hN₁eq : nbr G H y₁ = {x₁, x₂, w} := by
      apply eq_of_subset_of_card_le hN₁
      have := hdeg y₁ hy₁H
      have : #({x₁, x₂, w} : Finset V) ≤ 3 := card_le_three
      omega
    have hx₂N₁ : x₂ ∈ nbr G H y₁ := by rw [hN₁eq]; simp
    -- a third neighbour `x₃` of `v` outside `{x₁, x₂, w}`
    obtain ⟨x₃, hx₃⟩ : (nbr G H v \ {x₁, x₂, w}).Nonempty := by
      apply card_pos.1
      have := le_card_sdiff {x₁, x₂, w} (nbr G H v)
      have : #({x₁, x₂, w} : Finset V) ≤ 3 := card_le_three
      omega
    rw [mem_sdiff] at hx₃
    obtain ⟨hx₃, hx₃out⟩ := hx₃
    have hx₃H : x₃ ∈ H := mem_of_mem_nbr hx₃
    simp only [mem_insert, mem_singleton, not_or] at hx₃out hwx
    obtain ⟨hx₃x₁, hx₃x₂, hx₃w⟩ := hx₃out
    obtain ⟨hwx₁, hwx₂⟩ := hwx
    -- a neighbour `y₃ ≠ v` of `x₃`
    obtain ⟨y₃, hy₃⟩ : ((nbr G H x₃).erase v).Nonempty := by
      apply card_pos.1
      have := pred_card_le_card_erase (s := nbr G H x₃) (a := v)
      have := hdeg x₃ hx₃H
      omega
    rw [mem_erase] at hy₃
    obtain ⟨hy₃v, hy₃⟩ := hy₃
    have hy₃H : y₃ ∈ H := mem_of_mem_nbr hy₃
    -- `y₃ ≠ y₁`, since `x₃ ∈ N(y₃)` but `x₃ ∉ N(y₁)`
    have hx₃N₃ : x₃ ∈ nbr G H y₃ := nbr_symm hx₃H hy₃
    have hy₁₃ : y₁ ≠ y₃ := by
      rintro rfl
      have := hN₁ hx₃N₃
      simp only [mem_insert, mem_singleton] at this
      tauto
    -- `{x₂, w} ⊆ N(y₁) \ {x₁, x₃}`, so the latter has at least two elements
    have hsub : ({x₂, w} : Finset V) ⊆ nbr G H y₁ \ {x₁, x₃} := by
      intro u hu
      simp only [mem_insert, mem_singleton] at hu
      rw [mem_sdiff]
      simp only [mem_insert, mem_singleton, not_or]
      rcases hu with rfl | rfl
      · exact ⟨hx₂N₁, hx₁₂.symm, Ne.symm hx₃x₂⟩
      · exact ⟨hwN₁, hwx₁, Ne.symm hx₃w⟩
    have hB₁ : 2 ≤ #(nbr G H y₁ \ {x₁, x₃}) := by
      have := card_le_card hsub
      have : #({x₂, w} : Finset V) = 2 := card_pair (fun h => hwx₂ h.symm)
      omega
    have hB₃ : (nbr G H y₃ \ {x₁, x₃}).Nonempty := by
      apply card_pos.1
      have := le_card_sdiff {x₁, x₃} (nbr G H y₃)
      have := hdeg y₃ hy₃H
      have : #({x₁, x₃} : Finset V) ≤ 2 := card_le_two
      omega
    obtain ⟨z₁, hz₁, z₃, hz₃, hz₁₃⟩ := exists_ne_of_two_le_card hB₁ hB₃
    rw [mem_sdiff] at hz₁ hz₃
    exact hasSpiderAt_of_path H c hc hv hx₁ hx₃ (fun h => hx₃x₁ h.symm) hy₁ hy₃ hy₁v hy₃v hy₁₃
      hz₁.1 hz₃.1 hz₁.2 hz₃.2 hz₁₃

/-! ### The main theorem -/

/-- **Main theorem (Theorem 1.1).** Every bipartite graph `G` with more than `2·v(G)` edges
contains a copy of the spider `S(3,3,1)`. Bipartiteness is expressed by a proper 2-colouring
`c : V → Bool`. -/
theorem main (c : V → Bool) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (h : 2 * Fintype.card V < #G.edgeFinset) : ∃ v, HasSpiderAt G v := by
  have hd : 4 * #(univ : Finset V) < dsum G univ := by
    have h1 : dsum G univ = ∑ x, G.degree x := by
      unfold dsum
      refine sum_congr rfl fun x _ => ?_
      rw [nbr_univ, card_neighborFinset_eq_degree]
    rw [h1, G.sum_degrees_eq_twice_card_edges, card_univ]
    omega
  obtain ⟨H, -, -, hH, hdeg⟩ := core (G := G) univ hd
  obtain ⟨v, -, hv⟩ := exists_five_nbr H c hc hH
  exact ⟨v, hasSpiderAt_of_three_five H c hc hdeg hv⟩

end Spider

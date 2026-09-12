import Spider.AdditiveGap

/-!
# Trees on at most nine vertices (Section 7 and Corollary 1.2)

Following Waite–Aydin (arXiv:2607.29579), for a tree `T` and a vertex `x` let `S_T(x)` be the set
of neighbours `y` of `x` such that every neighbour of `y` other than `x` is a leaf; for
`T_{a,b} = (A, B)` with `a ≥ b` put `σ(T_{a,b}) = max_{x ∈ B} |S_T(x)|`. Their Theorem 1.4 proves
the fixed-part conjecture for every tree with `σ(T_{a,b}) ≥ min{a − b, b − 1}`.

* `Spider.card_leaves_add`, `Spider.sigma_lower` — Lemma 7.1: a tree with `a > b ≥ 1` has at
  least `a − b + 1` leaves in `A`, hence `b·σ ≥ a − b + 1` (equivalently `σ ≥ ⌈(a−b+1)/b⌉`).
* `Spider.census` — Proposition 7.2: a tree on at most nine vertices with
  `σ < min{a − b, b − 1}` has `(a, b) = (5, 3)` and is isomorphic to `S(3,3,1)`;
  `Spider.spider_isTree`, `Spider.spider_sigma` — conversely `S(3,3,1)` is such a tree.
* `Spider.corollary_nine`, `Spider.corollary_nine_order` — Corollary 1.2: *assuming* the
  Waite–Aydin theorem (Theorem 1.4, resp. Corollary 4.8), stated here as an explicit hypothesis,
  Conjecture 1.3 (resp. 1.2) holds for every tree on at most nine vertices.

Bipartitions are represented by a proper 2-colouring `c : V → Bool`; the class `B` is `cls c b` and
`A` is `cls c (!b)`.
-/

open Finset SimpleGraph

namespace Spider

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

/-! ### Colour classes, `S_T(x)` and `σ` -/

/-- The colour class `b` of a 2-colouring `c`. -/
def cls (c : V → Bool) (b : Bool) : Finset V := univ.filter (fun x => c x = b)

/-- `S_T(x)`: the neighbours `y` of `x` every neighbour of which other than `x` is a leaf of `T`,
i.e. the leaves and pendant preleaves attached to `x`. -/
def pendantSet (x : V) : Finset V :=
  (T.neighborFinset x).filter (fun y => ∀ z ∈ T.neighborFinset y, z ≠ x → T.degree z = 1)

/-- `σ(T_{a,b}) = max_{x ∈ B} |S_T(x)|` with `B = cls c b`. -/
def sigma (c : V → Bool) (b : Bool) : ℕ := (cls c b).sup (fun x => #(pendantSet T x))

/-- The leaves of `T` lying in the colour class `A = cls c (!b)`. -/
def leaves (c : V → Bool) (b : Bool) : Finset V := (cls c (!b)).filter (fun x => T.degree x = 1)

variable {T}

omit [Fintype V] [DecidableEq V] [DecidableRel T.Adj] in
lemma bool_not_ne (b : Bool) : (!b) ≠ b := by cases b <;> decide

omit [DecidableEq V] in
lemma mem_cls {c : V → Bool} {b : Bool} {x : V} : x ∈ cls c b ↔ c x = b := by simp [cls]

omit [DecidableEq V] in
lemma mem_leaves {c : V → Bool} {b : Bool} {x : V} :
    x ∈ leaves T c b ↔ x ∈ cls c (!b) ∧ T.degree x = 1 := by simp [leaves]

omit [DecidableEq V] in
lemma leaves_subset {c : V → Bool} {b : Bool} : leaves T c b ⊆ cls c (!b) := filter_subset _ _

omit [DecidableEq V] in
lemma card_cls_add_card_cls_not (c : V → Bool) (b : Bool) :
    #(cls c b) + #(cls c (!b)) = Fintype.card V := by
  have h : cls c (!b) = univ.filter (fun x => ¬ c x = b) := by
    ext x; simp [cls, Bool.eq_not_iff]
  rw [h, cls, card_filter_add_card_filter_not, card_univ]

omit [DecidableEq V] in
/-- Adjacent vertices lie in opposite classes: a vertex of `A` and a vertex of `B` are distinct. -/
lemma ne_of_mem_cls {c : V → Bool} {b : Bool} {x y : V} (hx : x ∈ cls c (!b)) (hy : y ∈ cls c b) :
    x ≠ y := by
  rintro rfl
  rw [mem_cls] at hx hy
  exact bool_not_ne b (hx.symm.trans hy)

/-- The sum of the degrees over one colour class is the number of edges (every edge has exactly
one endpoint in each class). -/
lemma sum_degree_cls (c : V → Bool) (hc : ∀ u w, T.Adj u w → c u ≠ c w) (b : Bool) :
    ∑ x ∈ cls c b, T.degree x = #T.edgeFinset := by
  have h1 := sum_nbr_side_eq (G := T) univ c hc b
  have h2 := sum_filter_add_sum_filter_not (univ : Finset V) (fun x => c x = b)
    (fun x => #(nbr T univ x))
  have h3 := T.sum_degrees_eq_twice_card_edges
  simp only [nbr_univ, card_neighborFinset_eq_degree] at h1 h2
  rw [h3] at h2
  unfold cls
  omega

omit [DecidableEq V] in
lemma degree_pos_of_isTree (hT : T.IsTree) (h2 : 2 ≤ Fintype.card V) (x : V) : 0 < T.degree x := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 h2
  exact hT.connected.preconnected.degree_pos_of_nontrivial x

/-! ### The neighbour of a leaf -/

/-- A chosen neighbour of `x` (any vertex if `x` is isolated); for a leaf it is *the* neighbour. -/
noncomputable def leafNbr (T : SimpleGraph V) [DecidableRel T.Adj] (x : V) : V :=
  if h : (T.neighborFinset x).Nonempty then h.choose else x

omit [DecidableEq V] in
lemma adj_leafNbr {x : V} (h : 0 < T.degree x) : T.Adj x (leafNbr T x) := by
  have hne : (T.neighborFinset x).Nonempty := by
    rw [← card_pos, card_neighborFinset_eq_degree]; exact h
  unfold leafNbr
  rw [dif_pos hne]
  exact (mem_neighborFinset _ _ _).1 hne.choose_spec

omit [DecidableEq V] in
lemma eq_leafNbr {x y : V} (h1 : T.degree x = 1) (hy : T.Adj x y) : y = leafNbr T x := by
  have hcard : #(T.neighborFinset x) = 1 := by rw [card_neighborFinset_eq_degree]; exact h1
  obtain ⟨a, ha⟩ := card_eq_one.1 hcard
  have hy' : y ∈ T.neighborFinset x := (mem_neighborFinset _ _ _).2 hy
  have hl : leafNbr T x ∈ T.neighborFinset x :=
    (mem_neighborFinset _ _ _).2 (adj_leafNbr (by omega))
  rw [ha, mem_singleton] at hy' hl
  rw [hy', hl]

/-- A leaf belongs to `S_T(y)` for its unique neighbour `y`. -/
lemma leaf_mem_pendantSet {x y : V} (h1 : T.degree x = 1) (hy : T.Adj x y) :
    x ∈ pendantSet T y := by
  rw [pendantSet, mem_filter, mem_neighborFinset]
  refine ⟨hy.symm, fun z hz hzy => ?_⟩
  rw [mem_neighborFinset] at hz
  exact absurd ((eq_leafNbr h1 hz).trans (eq_leafNbr h1 hy).symm) hzy

lemma card_pendantSet_le_sigma {c : V → Bool} {b : Bool} {y : V} (hy : y ∈ cls c b) :
    #(pendantSet T y) ≤ sigma T c b :=
  le_sup (f := fun x => #(pendantSet T x)) hy

omit [DecidableEq V] in
/-- The neighbour of a leaf of `A` lies in `B`. -/
lemma leafNbr_mem_cls {c : V → Bool} (hc : ∀ u w, T.Adj u w → c u ≠ c w) {b : Bool} {x : V}
    (hx : x ∈ leaves T c b) : leafNbr T x ∈ cls c b := by
  rw [mem_leaves, mem_cls] at hx
  rw [mem_cls]
  have h := hc _ _ (adj_leafNbr (T := T) (x := x) (by omega))
  rw [hx.1] at h
  exact bool_eq_of_ne_of_ne (bool_not_ne b) h

/-! ### Lemma 7.1 -/

/-- **Lemma 7.1 (first part).** A tree `T_{a,b}` with `a > b ≥ 1` has at least `a − b + 1` leaves
in `A`: `a + 1 ≤ |leaves in A| + b`. -/
theorem card_leaves_add (hT : T.IsTree) (c : V → Bool) (hc : ∀ u w, T.Adj u w → c u ≠ c w)
    (b : Bool) (hb1 : 1 ≤ #(cls c b)) (hab : #(cls c b) < #(cls c (!b))) :
    #(cls c (!b)) + 1 ≤ #(leaves T c b) + #(cls c b) := by
  have hcard := card_cls_add_card_cls_not c b
  have hE := hT.card_edgeFinset
  have hsum := sum_degree_cls c hc (!b)
  have hpos : ∀ x, 0 < T.degree x := degree_pos_of_isTree hT (by omega)
  have hle : ∑ x ∈ cls c (!b), (if T.degree x = 1 then 1 else 2) ≤ ∑ x ∈ cls c (!b), T.degree x := by
    refine sum_le_sum fun x _ => ?_
    have := hpos x
    split_ifs with h <;> omega
  rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at hle
  have hsplit := card_filter_add_card_filter_not (s := cls c (!b)) (fun x => T.degree x = 1)
  unfold leaves
  omega

/-- **Lemma 7.1 (second part).** For a tree `T_{a,b}` with `a > b ≥ 1`, `b·σ(T_{a,b}) ≥ a − b + 1`,
i.e. `σ ≥ ⌈(a − b + 1)/b⌉`. -/
theorem sigma_lower (hT : T.IsTree) (c : V → Bool) (hc : ∀ u w, T.Adj u w → c u ≠ c w)
    (b : Bool) (hb1 : 1 ≤ #(cls c b)) (hab : #(cls c b) < #(cls c (!b))) :
    #(cls c (!b)) + 1 ≤ #(cls c b) * sigma T c b + #(cls c b) := by
  have hL := card_leaves_add hT c hc b hb1 hab
  have hmaps : Set.MapsTo (leafNbr T) ↑(leaves T c b) ↑(cls c b) := fun x hx =>
    mem_coe.2 (leafNbr_mem_cls hc (mem_coe.1 hx))
  have hfib : ∀ y ∈ cls c b,
      #((leaves T c b).filter (fun x => leafNbr T x = y)) ≤ sigma T c b := by
    intro y hy
    refine le_trans (card_le_card (t := pendantSet T y) ?_) (card_pendantSet_le_sigma hy)
    intro x hx
    rw [mem_filter, mem_leaves] at hx
    obtain ⟨⟨-, hx1⟩, hxy⟩ := hx
    have := leaf_mem_pendantSet hx1 (adj_leafNbr (T := T) (x := x) (by omega))
    rwa [hxy] at this
  have h1 := card_eq_sum_card_fiberwise hmaps
  have h2 := sum_le_sum hfib
  rw [sum_const, smul_eq_mul] at h2
  omega

/-! ### From an explicit spider to an isomorphism -/

/-- A graph on eight vertices with seven edges containing a spider centred at `v` is isomorphic to
the spider. -/
noncomputable def isoOfHasSpiderAt {v : V} (h8 : Fintype.card V = 8) (h7 : #T.edgeFinset = 7)
    (h : HasSpiderAt T v) : T ≃g spider := by
  choose x₁ y₁ z₁ x₂ y₂ z₂ x₄ hnd h1 h2 h3 h4 h5 h6 h7' using h
  let f : Fin 8 → V := ![v, x₁, y₁, z₁, x₂, y₂, z₂, x₄]
  have hf : Function.Injective f := by
    rw [← List.nodup_ofFn]
    simpa [f, List.ofFn_succ] using hnd
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [h8]⟩
  have hfwd : ∀ i j, spider.Adj i j → T.Adj (f i) (f j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact h1 | exact h1.symm | exact h2 | exact h2.symm | exact h3 | exact h3.symm
      | exact h4 | exact h4.symm | exact h5 | exact h5.symm | exact h6 | exact h6.symm
      | exact h7' | exact h7'.symm
  have hsub : spider.edgeFinset.map ⟨Sym2.map f, Sym2.map.injective hf⟩ ⊆ T.edgeFinset := by
    intro e he
    rw [mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    revert he'
    induction e' using Sym2.ind with
    | h i j =>
      intro he'
      rw [mem_edgeFinset, mem_edgeSet] at he'
      simp only [Function.Embedding.coeFn_mk, Sym2.map_mk, mem_edgeFinset, mem_edgeSet]
      exact hfwd i j he'
  have hEeq : spider.edgeFinset.map ⟨Sym2.map f, Sym2.map.injective hf⟩ = T.edgeFinset := by
    apply eq_of_subset_of_card_le hsub
    rw [card_map, h7]
    decide
  have hbwd : ∀ i j, T.Adj (f i) (f j) → spider.Adj i j := by
    intro i j hij
    have hmem : s(f i, f j) ∈ T.edgeFinset := by rw [mem_edgeFinset, mem_edgeSet]; exact hij
    rw [← hEeq, mem_map] at hmem
    obtain ⟨e, he, hee⟩ := hmem
    simp only [Function.Embedding.coeFn_mk] at hee
    rw [← Sym2.map_mk] at hee
    rw [Sym2.map.injective hf hee, mem_edgeFinset, mem_edgeSet] at he
    exact he
  exact (RelIso.mk (Equiv.ofBijective f hbij) (fun {i j} => ⟨hbwd i j, hfwd i j⟩)).symm

/-! ### Proposition 7.2 -/

/-- **Proposition 7.2.** A tree on at most nine vertices with `σ(T_{a,b}) < min{a − b, b − 1}` has
part-sizes `(a, b) = (5, 3)` and is isomorphic to the spider `S(3,3,1)`. -/
theorem census (hT : T.IsTree) (c : V → Bool) (hc : ∀ u w, T.Adj u w → c u ≠ c w) (b : Bool)
    (hb : #(cls c b) ≤ #(cls c (!b))) (h9 : Fintype.card V ≤ 9)
    (hσ : sigma T c b < min (#(cls c (!b)) - #(cls c b)) (#(cls c b) - 1)) :
    #(cls c (!b)) = 5 ∧ #(cls c b) = 3 ∧ Nonempty (T ≃g spider) := by
  have hcard := card_cls_add_card_cls_not c b
  have hab : #(cls c b) < #(cls c (!b)) := by omega
  have hb1 : 1 ≤ #(cls c b) := by omega
  have hsig := sigma_lower hT c hc b hb1 hab
  have hσpos : 1 ≤ sigma T c b := by
    rcases Nat.eq_zero_or_pos (sigma T c b) with h0 | h0
    · rw [h0, mul_zero] at hsig; omega
    · exact h0
  have hb3 : #(cls c b) = 3 := by omega
  rw [hb3] at hsig
  have ha5 : #(cls c (!b)) = 5 := by omega
  have hσ1 : sigma T c b ≤ 1 := by omega
  refine ⟨ha5, hb3, ?_⟩
  have h8 : Fintype.card V = 8 := by omega
  have hE : #T.edgeFinset = 7 := by have := hT.card_edgeFinset; omega
  have hpos : ∀ x, 0 < T.degree x := degree_pos_of_isTree hT (by omega)
  have hL := card_leaves_add hT c hc b hb1 hab
  -- the leaf-neighbour map `L → B` is injective, because `σ ≤ 1`
  have hinj : ∀ x ∈ leaves T c b, ∀ y ∈ leaves T c b, leafNbr T x = leafNbr T y → x = y := by
    intro x hx y hy hxy
    have hx1 : T.degree x = 1 := (mem_leaves.1 hx).2
    have hy1 : T.degree y = 1 := (mem_leaves.1 hy).2
    have hxm := leaf_mem_pendantSet hx1 (adj_leafNbr (T := T) (x := x) (by omega))
    have hym := leaf_mem_pendantSet hy1 (adj_leafNbr (T := T) (x := y) (by omega))
    rw [← hxy] at hym
    have hle : #(pendantSet T (leafNbr T x)) ≤ 1 :=
      (card_pendantSet_le_sigma (leafNbr_mem_cls hc hx)).trans hσ1
    exact card_le_one_iff.1 hle hxm hym
  have hLcard : #(leaves T c b) ≤ #(cls c b) :=
    card_le_card_of_injOn (leafNbr T) (fun x hx => mem_coe.2 (leafNbr_mem_cls hc (mem_coe.1 hx)))
      (fun x hx y hy hxy => hinj x (mem_coe.1 hx) y (mem_coe.1 hy) hxy)
  have hL3 : #(leaves T c b) = 3 := by omega
  -- hence it is a bijection onto `B`: every vertex of `B` carries exactly one leaf of `A`
  have hsurj : ∀ y ∈ cls c b, ∃ x ∈ leaves T c b, leafNbr T x = y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := surj_on_of_inj_on_of_card_le (s := leaves T c b) (t := cls c b)
      (fun x _ => leafNbr T x) (fun x hx => leafNbr_mem_cls hc hx)
      (fun x₁ x₂ hx₁ hx₂ h => hinj x₁ hx₁ x₂ hx₂ h) (by omega) y hy
    exact ⟨x, hx, hxy.symm⟩
  -- the two non-leaf vertices `u, u'` of `A` have degree exactly `2`
  have hAL : leaves T c b ⊆ cls c (!b) := leaves_subset
  have hUcard : #(cls c (!b) \ leaves T c b) = 2 := by
    have := card_sdiff_add_card_eq_card hAL
    omega
  obtain ⟨u, u', huu', hU⟩ := card_eq_two.1 hUcard
  have hu : u ∈ cls c (!b) \ leaves T c b := by rw [hU]; simp
  have hu' : u' ∈ cls c (!b) \ leaves T c b := by rw [hU]; simp
  rw [mem_sdiff] at hu hu'
  have hsumA := sum_degree_cls c hc (!b)
  have hsplit : ∑ x ∈ cls c (!b) \ leaves T c b, T.degree x + ∑ x ∈ leaves T c b, T.degree x
      = ∑ x ∈ cls c (!b), T.degree x := sum_sdiff hAL
  have hsumL : ∑ x ∈ leaves T c b, T.degree x = 3 := by
    rw [sum_congr rfl (fun x hx => (mem_leaves.1 hx).2), sum_const, smul_eq_mul, hL3]
  have hsumU : ∑ x ∈ cls c (!b) \ leaves T c b, T.degree x = T.degree u + T.degree u' := by
    rw [hU, sum_pair huu']
  have hdu1 : T.degree u ≠ 1 := fun h => hu.2 (mem_leaves.2 ⟨hu.1, h⟩)
  have hdu'1 : T.degree u' ≠ 1 := fun h => hu'.2 (mem_leaves.2 ⟨hu'.1, h⟩)
  have hdu : T.degree u = 2 := by have := hpos u; have := hpos u'; omega
  have hdu' : T.degree u' = 2 := by have := hpos u; have := hpos u'; omega
  -- their neighbourhoods are two-element subsets of `B`
  have hNu : T.neighborFinset u ⊆ cls c b := by
    intro y hy
    rw [mem_neighborFinset] at hy
    rw [mem_cls]
    have h := hc _ _ hy
    rw [mem_cls.1 hu.1] at h
    exact bool_eq_of_ne_of_ne (bool_not_ne b) h
  have hNu' : T.neighborFinset u' ⊆ cls c b := by
    intro y hy
    rw [mem_neighborFinset] at hy
    rw [mem_cls]
    have h := hc _ _ hy
    rw [mem_cls.1 hu'.1] at h
    exact bool_eq_of_ne_of_ne (bool_not_ne b) h
  have hNuc : #(T.neighborFinset u) = 2 := by rw [card_neighborFinset_eq_degree]; exact hdu
  have hNu'c : #(T.neighborFinset u') = 2 := by rw [card_neighborFinset_eq_degree]; exact hdu'
  -- `N(u) ≠ N(u')`: otherwise there would be two distinct paths from `u` to `u'`
  have hNne : T.neighborFinset u ≠ T.neighborFinset u' := by
    intro heq
    obtain ⟨y₁, y₂, hy12, hNu2⟩ := card_eq_two.1 hNuc
    have h1 : T.Adj u y₁ := by rw [← mem_neighborFinset, hNu2]; simp
    have h2 : T.Adj u y₂ := by rw [← mem_neighborFinset, hNu2]; simp
    have h1' : T.Adj y₁ u' := by rw [adj_comm, ← mem_neighborFinset, ← heq, hNu2]; simp
    have h2' : T.Adj y₂ u' := by rw [adj_comm, ← mem_neighborFinset, ← heq, hNu2]; simp
    obtain ⟨-, huniq⟩ := isTree_iff_existsUnique_path.1 hT
    obtain ⟨p, -, hp⟩ := huniq u u'
    let w₁ : T.Walk u u' := Walk.cons h1 (Walk.cons h1' Walk.nil)
    let w₂ : T.Walk u u' := Walk.cons h2 (Walk.cons h2' Walk.nil)
    have hw₁ : w₁.IsPath := by
      simp [w₁, Walk.cons_isPath_iff, h1.ne, h1'.ne, huu']
    have hw₂ : w₂.IsPath := by
      simp [w₂, Walk.cons_isPath_iff, h2.ne, h2'.ne, huu']
    have hw : w₁ = w₂ := (hp w₁ hw₁).trans (hp w₂ hw₂).symm
    have := congrArg Walk.support hw
    simp [w₁, w₂] at this
    exact hy12 this
  -- a common neighbour `xc` (the centre) and the two private neighbours `p`, `q`
  obtain ⟨xc, hxc⟩ : (T.neighborFinset u ∩ T.neighborFinset u').Nonempty := by
    rw [← card_pos]
    have h1 := card_union_add_card_inter (T.neighborFinset u) (T.neighborFinset u')
    have h2 : #(T.neighborFinset u ∪ T.neighborFinset u') ≤ #(cls c b) :=
      card_le_card (union_subset hNu hNu')
    omega
  rw [mem_inter] at hxc
  obtain ⟨p, hp, hpxc⟩ := exists_mem_ne (s := T.neighborFinset u) (by omega) xc
  obtain ⟨q, hq, hqxc⟩ := exists_mem_ne (s := T.neighborFinset u') (by omega) xc
  have hNu_eq : T.neighborFinset u = {xc, p} := by
    symm
    apply eq_of_subset_of_card_le
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hxc.1
      · exact hp
    · rw [card_pair hpxc.symm]; omega
  have hNu'_eq : T.neighborFinset u' = {xc, q} := by
    symm
    apply eq_of_subset_of_card_le
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hxc.2
      · exact hq
    · rw [card_pair hqxc.symm]; omega
  have hpq : p ≠ q := by
    intro h
    apply hNne
    rw [hNu_eq, hNu'_eq, h]
  -- memberships in `B`
  have hxcB : xc ∈ cls c b := hNu hxc.1
  have hpB : p ∈ cls c b := hNu hp
  have hqB : q ∈ cls c b := hNu' hq
  -- the leaves attached to `p`, `xc`, `q`
  obtain ⟨lp, hlp, hlpn⟩ := hsurj p hpB
  obtain ⟨lc, hlc, hlcn⟩ := hsurj xc hxcB
  obtain ⟨lq, hlq, hlqn⟩ := hsurj q hqB
  have hlpA : lp ∈ cls c (!b) := (mem_leaves.1 hlp).1
  have hlcA : lc ∈ cls c (!b) := (mem_leaves.1 hlc).1
  have hlqA : lq ∈ cls c (!b) := (mem_leaves.1 hlq).1
  -- adjacencies
  have a_uxc : T.Adj u xc := (mem_neighborFinset _ _ _).1 hxc.1
  have a_u'xc : T.Adj u' xc := (mem_neighborFinset _ _ _).1 hxc.2
  have a_up : T.Adj u p := (mem_neighborFinset _ _ _).1 hp
  have a_u'q : T.Adj u' q := (mem_neighborFinset _ _ _).1 hq
  have a_lpp : T.Adj lp p := by
    have := adj_leafNbr (T := T) (x := lp) (by rw [(mem_leaves.1 hlp).2]; omega)
    rwa [hlpn] at this
  have a_lcxc : T.Adj lc xc := by
    have := adj_leafNbr (T := T) (x := lc) (by rw [(mem_leaves.1 hlc).2]; omega)
    rwa [hlcn] at this
  have a_lqq : T.Adj lq q := by
    have := adj_leafNbr (T := T) (x := lq) (by rw [(mem_leaves.1 hlq).2]; omega)
    rwa [hlqn] at this
  -- distinctness
  have hlplc : lp ≠ lc := fun h => hpxc (by rw [← hlpn, ← hlcn, h])
  have hlplq : lp ≠ lq := fun h => hpq (by rw [← hlpn, ← hlqn, h])
  have hlclq : lc ≠ lq := fun h => hqxc (by rw [← hlqn, ← hlcn, h])
  have hulp : u ≠ lp := fun h => hu.2 (h ▸ hlp)
  have hulc : u ≠ lc := fun h => hu.2 (h ▸ hlc)
  have hulq : u ≠ lq := fun h => hu.2 (h ▸ hlq)
  have hu'lp : u' ≠ lp := fun h => hu'.2 (h ▸ hlp)
  have hu'lc : u' ≠ lc := fun h => hu'.2 (h ▸ hlc)
  have hu'lq : u' ≠ lq := fun h => hu'.2 (h ▸ hlq)
  -- assemble the spider centred at `xc`: arms `xc — u — p — lp`, `xc — u' — q — lq`, leaf `lc`
  have hsp : HasSpiderAt T xc := by
    refine ⟨u, p, lp, u', q, lq, lc, ?_, a_uxc.symm, a_up, a_lpp.symm, a_u'xc.symm, a_u'q,
      a_lqq.symm, a_lcxc.symm⟩
    have d01 : xc ≠ u := (ne_of_mem_cls hu.1 hxcB).symm
    have d02 : xc ≠ p := hpxc.symm
    have d03 : xc ≠ lp := (ne_of_mem_cls hlpA hxcB).symm
    have d04 : xc ≠ u' := (ne_of_mem_cls hu'.1 hxcB).symm
    have d05 : xc ≠ q := hqxc.symm
    have d06 : xc ≠ lq := (ne_of_mem_cls hlqA hxcB).symm
    have d07 : xc ≠ lc := (ne_of_mem_cls hlcA hxcB).symm
    have d12 : u ≠ p := ne_of_mem_cls hu.1 hpB
    have d13 : u ≠ lp := hulp
    have d14 : u ≠ u' := huu'
    have d15 : u ≠ q := ne_of_mem_cls hu.1 hqB
    have d16 : u ≠ lq := hulq
    have d17 : u ≠ lc := hulc
    have d23 : p ≠ lp := (ne_of_mem_cls hlpA hpB).symm
    have d24 : p ≠ u' := (ne_of_mem_cls hu'.1 hpB).symm
    have d25 : p ≠ q := hpq
    have d26 : p ≠ lq := (ne_of_mem_cls hlqA hpB).symm
    have d27 : p ≠ lc := (ne_of_mem_cls hlcA hpB).symm
    have d34 : lp ≠ u' := hu'lp.symm
    have d35 : lp ≠ q := ne_of_mem_cls hlpA hqB
    have d36 : lp ≠ lq := hlplq
    have d37 : lp ≠ lc := hlplc
    have d45 : u' ≠ q := ne_of_mem_cls hu'.1 hqB
    have d46 : u' ≠ lq := hu'lq
    have d47 : u' ≠ lc := hu'lc
    have d56 : q ≠ lq := (ne_of_mem_cls hlqA hqB).symm
    have d57 : q ≠ lc := (ne_of_mem_cls hlcA hqB).symm
    have d67 : lq ≠ lc := hlclq.symm
    simp [List.nodup_cons, d01, d02, d03, d04, d05, d06, d07, d12, d13, d14, d15, d16, d17,
      d23, d24, d25, d26, d27, d34, d35, d36, d37, d45, d46, d47, d56, d57, d67]
  exact ⟨isoOfHasSpiderAt h8 hE hsp⟩

/-! ### The spider itself -/

/-- The bipartition of the spider: `B = {0, 2, 5}` (colour `false`) and `A = {1, 3, 4, 6, 7}`
(colour `true`). -/
def spiderColour : Fin 8 → Bool := ![false, true, false, true, true, false, true, true]

lemma spiderColour_proper : ∀ u w, spider.Adj u w → spiderColour u ≠ spiderColour w := by decide

lemma spider_card_cls : #(cls spiderColour false) = 3 ∧ #(cls spiderColour true) = 5 := by decide

/-- `σ(S(3,3,1)) = 1`: each vertex of the smaller class has exactly one pendant neighbour. -/
lemma spider_sigma : sigma spider spiderColour false = 1 := by decide

lemma spider_connected : spider.Connected := by
  have h0 : ∀ v : Fin 8, spider.Reachable 0 v := by
    intro v
    fin_cases v
    · exact Reachable.refl _
    · exact (Walk.cons (by decide : spider.Adj 0 1) Walk.nil).reachable
    · exact (Walk.cons (by decide : spider.Adj 0 1)
        (Walk.cons (by decide : spider.Adj 1 2) Walk.nil)).reachable
    · exact (Walk.cons (by decide : spider.Adj 0 1) (Walk.cons (by decide : spider.Adj 1 2)
        (Walk.cons (by decide : spider.Adj 2 3) Walk.nil))).reachable
    · exact (Walk.cons (by decide : spider.Adj 0 4) Walk.nil).reachable
    · exact (Walk.cons (by decide : spider.Adj 0 4)
        (Walk.cons (by decide : spider.Adj 4 5) Walk.nil)).reachable
    · exact (Walk.cons (by decide : spider.Adj 0 4) (Walk.cons (by decide : spider.Adj 4 5)
        (Walk.cons (by decide : spider.Adj 5 6) Walk.nil))).reachable
    · exact (Walk.cons (by decide : spider.Adj 0 7) Walk.nil).reachable
  exact Connected.mk fun u v => (h0 u).symm.trans (h0 v)

/-- `S(3,3,1)` is a tree. -/
theorem spider_isTree : spider.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨spider_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
  decide

/-- **Proposition 7.2 (converse).** `S(3,3,1)` is a tree on eight vertices with `(a, b) = (5, 3)`
and `σ = 1 < 2 = min{a − b, b − 1}`. -/
theorem spider_outside_criterion :
    spider.IsTree ∧ Fintype.card (Fin 8) ≤ 9 ∧
    #(cls spiderColour false) ≤ #(cls spiderColour true) ∧
    sigma spider spiderColour false <
      min (#(cls spiderColour true) - #(cls spiderColour false)) (#(cls spiderColour false) - 1) := by
  refine ⟨spider_isTree, by decide, ?_, ?_⟩
  · rw [spider_card_cls.1, spider_card_cls.2]; decide
  · rw [spider_sigma, spider_card_cls.1, spider_card_cls.2]; decide

/-! ### Corollary 1.2, conditional on the Waite–Aydin theorem -/

/-- The right-hand side of Waite–Aydin Conjecture 1.3 / Theorem 1.4 for `T_{a,b}` and part-sizes
`m ≤ n`: `(b − 1)n + (a − b)m` if `a ≥ 2b − 1`, and `(b − 1)n + (b − 1)m` if `a ≤ 2b − 1`. -/
def waBound (a b m n : ℕ) : ℕ :=
  (b - 1) * n + (if 2 * b ≤ a + 1 then (a - b) * m else (b - 1) * m)

/-- **Waite–Aydin, Theorem 1.4 (fixed-part form), as a hypothesis.** For every tree `T_{a,b}` with
`σ(T_{a,b}) ≥ min{a − b, b − 1}` and all `m ≤ n`, every `T`-free bipartite graph with parts
`Fin m`, `Fin n` has at most `waBound a b m n` edges. This is an external theorem, not
formalised here; Corollary 1.2 is proved *assuming* it. -/
def WaiteAydinThm14 : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
    T.IsTree → ∀ (c : W → Bool), (∀ u w, T.Adj u w → c u ≠ c w) → ∀ (b : Bool),
    #(cls c b) ≤ #(cls c (!b)) →
    min (#(cls c (!b)) - #(cls c b)) (#(cls c b) - 1) ≤ sigma T c b →
    ∀ (m n : ℕ), m ≤ n → ∀ (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj],
      (∀ x y, G.Adj x y → x.isLeft ≠ y.isLeft) → T.Free G →
      #G.edgeFinset ≤ waBound (#(cls c (!b))) (#(cls c b)) m n

/-- **Corollary 1.2 (fixed-part form), conditional on Waite–Aydin Theorem 1.4.** Conjecture 1.3
of Waite–Aydin holds for every tree on at most nine vertices. -/
theorem corollary_nine (WA : WaiteAydinThm14.{u})
    (hT : T.IsTree) (h9 : Fintype.card V ≤ 9)
    (c : V → Bool) (hc : ∀ u w, T.Adj u w → c u ≠ c w) (b : Bool)
    (hb : #(cls c b) ≤ #(cls c (!b)))
    (m n : ℕ) (hmn : m ≤ n) (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj]
    (hcross : ∀ x y, G.Adj x y → x.isLeft ≠ y.isLeft) (hfree : T.Free G) :
    #G.edgeFinset ≤ waBound (#(cls c (!b))) (#(cls c b)) m n := by
  by_cases hσ : min (#(cls c (!b)) - #(cls c b)) (#(cls c b) - 1) ≤ sigma T c b
  · exact WA T hT c hc b hb hσ m n hmn G hcross hfree
  · push Not at hσ
    obtain ⟨ha, hb', ⟨iso⟩⟩ := census hT c hc b hb h9 hσ
    have hfree' : spider.Free G := fun h => hfree (IsContained.trans ⟨iso.toCopy⟩ h)
    have := exbip_le m n G hcross hfree'
    rw [ha, hb']
    simp [waBound]
    omega

/-- Twice the right-hand side of Waite–Aydin Conjecture 1.2 / Corollary 4.8 for `T_{a,b}` on a
host of order `N`: `(a − 1)N` if `a ≥ 2b − 1`, and `2(b − 1)N` if `a ≤ 2b − 1`. -/
def waOrderBound2 (a b N : ℕ) : ℕ := if 2 * b ≤ a + 1 then (a - 1) * N else 2 * (b - 1) * N

/-- **Waite–Aydin, Corollary 4.8 (order form), as a hypothesis.** For every tree `T_{a,b}` with
`σ(T_{a,b}) ≥ min{a − b, b − 1}`, every `T`-free bipartite graph on `N` vertices has at most
`waOrderBound2 a b N / 2` edges. -/
def WaiteAydinCor48 : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
    T.IsTree → ∀ (c : W → Bool), (∀ u w, T.Adj u w → c u ≠ c w) → ∀ (b : Bool),
    #(cls c b) ≤ #(cls c (!b)) →
    min (#(cls c (!b)) - #(cls c b)) (#(cls c b) - 1) ≤ sigma T c b →
    ∀ {X : Type u} [Fintype X] [DecidableEq X] (G : SimpleGraph X) [DecidableRel G.Adj]
      (c' : X → Bool), (∀ x y, G.Adj x y → c' x ≠ c' y) → T.Free G →
      2 * #G.edgeFinset ≤ waOrderBound2 (#(cls c (!b))) (#(cls c b)) (Fintype.card X)

/-- **Corollary 1.2 (order form), conditional on Waite–Aydin Corollary 4.8.** Conjecture 1.2 of
Waite–Aydin holds for every tree on at most nine vertices. -/
theorem corollary_nine_order (WA : WaiteAydinCor48.{u})
    (hT : T.IsTree) (h9 : Fintype.card V ≤ 9)
    (c : V → Bool) (hc : ∀ u w, T.Adj u w → c u ≠ c w) (b : Bool)
    (hb : #(cls c b) ≤ #(cls c (!b)))
    {X : Type u} [Fintype X] [DecidableEq X] (G : SimpleGraph X) [DecidableRel G.Adj]
    (c' : X → Bool) (hc' : ∀ x y, G.Adj x y → c' x ≠ c' y) (hfree : T.Free G) :
    2 * #G.edgeFinset ≤ waOrderBound2 (#(cls c (!b))) (#(cls c b)) (Fintype.card X) := by
  by_cases hσ : min (#(cls c (!b)) - #(cls c b)) (#(cls c b) - 1) ≤ sigma T c b
  · exact WA T hT c hc b hb hσ G c' hc' hfree
  · push Not at hσ
    obtain ⟨ha, hb', ⟨iso⟩⟩ := census hT c hc b hb h9 hσ
    have hfree' : spider.Free G := fun h => hfree (IsContained.trans ⟨iso.toCopy⟩ h)
    have := edge_bound c' hc' hfree'
    rw [ha, hb']
    simp [waOrderBound2]
    omega

end Spider

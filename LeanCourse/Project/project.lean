/- This file contains the proof that any (multiplicative) group of order 8
is isomorphic to (the multiplicative version of) one of  `ZMod 8`,
`(ZMod 4) × (ZMod 2)`, `ZMod 2 × ZMod 2 × ZMod 2`, `DihedralGroup 4`, `QuaternionGroup 2`.
The proofs that these five groups are pairwise non-isomorphic is in a separate file, nonisomorphic.lean -/


import LeanCourse.Common
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Data.Set.Card


@[simp]
lemma one_zmod2_eq_one: (1:ZMod 2).val = 1 := rfl

@[simp]
lemma one_zmod4_eq_one: (1:ZMod 4).val = 1 := rfl

@[simp]
lemma two_zmod4_eq_two: (2:ZMod 4).val = 2 := rfl

@[simp]
lemma three_zmod4_eq_three: (3:ZMod 4).val = 3 := rfl

@[simp]
lemma neg_one_zmod4_eq_three: (-1:ZMod 4).val = 3 := rfl

@[simp]
lemma neg_two_zmod4_eq_two: (-2:ZMod 4).val = 2 := rfl

@[simp]
lemma neg_three_zmod4_eq_one: (-3:ZMod 4).val = 1 := rfl


lemma zmod_four_val_eq_self: ∀ (i:ZMod 4), (i.val :ZMod 4) = i := by decide
lemma zmod_eight_val_eq_self: ∀ (i:ZMod 8), (i.val :ZMod 8) = i := by decide

lemma zmod_four_eq_of_eq_pow{G:Type*}[Group G]{a:G}(ha: orderOf a = 4):∀ (i j :ZMod 4),a ^ i.val = a^j.val → i = j:= by
    intro i j hij
    rw[← zmod_four_val_eq_self i, ← zmod_four_val_eq_self j]
    rw [pow_inj_mod,ha] at hij
    rw [ZMod.nat_cast_eq_nat_cast_iff']
    exact hij

lemma zmod_eight_eq_of_eq_pow{G:Type*}[Group G]{a:G}(ha: orderOf a = 8):∀ (i j :ZMod 8),a ^ i.val = a^j.val → i = j:= by
    intro i j hij
    rw[← zmod_eight_val_eq_self i, ← zmod_eight_val_eq_self j]
    rw [pow_inj_mod,ha] at hij
    rw [ZMod.nat_cast_eq_nat_cast_iff']
    exact hij

lemma pow_eq_pow_zmod{G:Type*}[Group G]{a: G}{k:ℕ}(ha: orderOf a = k)(n:ℕ): a ^ n = a^((n:ZMod k).val ):= by
  rw[ZMod.val_nat_cast n]
  rw[← ha]
  exact pow_eq_mod_orderOf

lemma zmod_two_val_add_eq   : ∀ (i j :ZMod 2), (i+j).val = ((i.val + j.val):ZMod 2).val := by decide
lemma zmod_four_val_add_eq  : ∀ (i j :ZMod 4), (i+j).val = ((i.val + j.val):ZMod 4).val := by decide
lemma zmod_eight_val_add_eq : ∀ (i j :ZMod 8), (i+j).val = ((i.val + j.val):ZMod 8).val := by decide

lemma zmod_four_pow_val_sum_eq_pow_sum_val{G:Type*}[Group G]{g:G}(hg:orderOf g = 4): ∀ (i j :ZMod 4), g ^ ((i + j).val) = g ^ (i.val + j.val):= by
    intro i j
    rw[pow_eq_pow_zmod hg (i.val+j.val),zmod_four_val_add_eq i j]
    simp

lemma zmod_eight_pow_val_sum_eq_pow_sum_val{G:Type*}[Group G]{g:G}(hg:orderOf g = 8): ∀ (i j :ZMod 8), g ^ ((i + j).val) = g ^ (i.val + j.val):= by
    intro i j
    rw[pow_eq_pow_zmod hg (i.val+j.val),zmod_eight_val_add_eq i j]
    simp


open Function


lemma groups_isom_of_injective_hom{G A: Type*}[hG: Group G][Fintype G][Group A][Fintype A](hG: Fintype.card G = 8)(hA: Fintype.card A = 8)(f:A →* G)(hf: Injective f): Nonempty (G ≃* A):= by
  have hf1: Bijective f:= by
    apply (Fintype.bijective_iff_injective_and_card f).2 ⟨hf,by simp[hG,hA]⟩
  let f_equiv_mul: A ≃* G :={ Equiv.ofBijective f hf1 with map_mul' := by refine fun x y ↦ f.map_mul' x y}
  exact Nonempty.intro (id (MulEquiv.symm f_equiv_mul))


/-- If a group of order 8 has an element of order 8, then it is isomorphic to (the multiplicative version of)  `ZMod 8` -/
lemma zmod8_of_elt_order_eight {G : Type*} [Group G][Fintype G](hG: Fintype.card G = 8){g:G}(hg: orderOf g = 8): Nonempty (G ≃* Multiplicative (ZMod 8)):= by {
  let f := fun (n:ZMod 8) ↦ (g ^ n.val)
  have hf1: Injective f:= by
    intro x y hxy
    simp at hxy
    exact zmod_eight_eq_of_eq_pow hg x y hxy
  have hf2: Bijective f:= by
    apply (Fintype.bijective_iff_injective_and_card f).2 ⟨hf1, (by simp[hG])⟩
  have hf3: ∀ (x y : ZMod 8), f (x + y) = f x *  f y := by
    intro x y
    simp
    rw[zmod_eight_pow_val_sum_eq_pow_sum_val hg x y,pow_add g x.val]
  let f_equiv_mul: (Multiplicative (ZMod 8)) ≃* G :={Equiv.ofBijective f hf2 with map_mul' := by exact fun x y ↦ hf3 x y}
  exact Nonempty.intro (id (MulEquiv.symm f_equiv_mul))
}


/-- If `G` is a commutative group and `f : M → G` and `g : N → G` are injective group homomorphisms with their images intersecting only in the identity element, then the map `(m,n) ↦ f(m)*g(n)` is injective -/
lemma monoid_hom_coprod_injective_of_injective{G M N: Type*}[CommGroup G][Group M][Group N](f:M →* G)(hf: Injective f)(g: N →* G)(hg: Injective g)(hfg: f.range ⊓ g.range  = ⊥): Injective (MonoidHom.coprod f g):= by
  rw[injective_iff_map_eq_one]
  intro x hx
  simp at hx
  rw[mul_eq_one_iff_inv_eq] at hx
  have h1: f x.1 ∈ f.range ⊓ g.range := by
    constructor
    · simp
    · use x.2⁻¹; simp; rw[← hx]; simp
  simp[hfg] at h1
  have hx1: x.1 = 1 := by apply (injective_iff_map_eq_one f).1 hf x.1 h1
  have h2: g x.2 ∈ f.range ⊓ g.range := by
    constructor
    · use x.1⁻¹; rw[← hx]; simp
    · simp
  simp[hfg] at h2
  have hx2: x.2 = 1:= by apply (injective_iff_map_eq_one g).1 hg x.2 h2
  exact Prod.ext (hf (congrArg f (hf (congrArg f hx1)))) (hg (congrArg g (hg (congrArg g hx2))))


/-- A group where every non-identity element has order 2 is abelian -/
lemma comm_of_elts_order_two{G : Type*}[Group G](h: ∀ g:G, g ≠ 1 → orderOf g = 2): IsCommutative G (fun x y ↦ x*y) where
  comm := by
    intro a b
    have h1: ∀ g:G, g*g = 1 := by{
      intro g
      by_cases hg: g = 1
      · simp[hg]
      · rw [← pow_two, ← h g hg, pow_orderOf_eq_one]
    }
    calc
      a * b = (a * b) * (a * b) * b⁻¹ * a⁻¹ := by group
      _ = 1 * b⁻¹ * (b*b) * a⁻¹ * (a*a) := by rw[h1 (a*b), h1 b, h1 a]; group
      _ = b * a := by group


lemma two_distinct_elts{G : Type*}[Group G][Fintype G](hG: Fintype.card G = 8): ∃ (a b : G), a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 := by
  have hG4: 2 < Fintype.card G :=by simp[hG]
  obtain ⟨a,b,c,habc⟩ := Fintype.two_lt_card_iff.1 hG4
  by_cases hc: c = 1
  · use a; use b
    rw[← hc]
    exact habc
  · by_cases hb: b = 1
    · use a; use c
      rw[← hb]
      simp[habc]
      rw[hb]
      exact hc
    · use b; use c
      simp[habc,hb,hc]

lemma third_distinct_elt{G : Type*}[Group G][Fintype G](hG: Fintype.card G = 8){a b :G}(hab: a ≠ b)(ha1: a ≠ 1)(hb1: b ≠ 1):  ∃ c ∈ (Set.univ:Set G), c ∉ ({(1:G),a,b,a*b}:Set G) := by
  classical
  have h1: Finset.card ({(1:G),a,b,a*b}:Finset G) ≤ 4:= by
    apply le_trans (Finset.card_insert_le _ _) _
    simp[*]
  apply Set.exists_mem_not_mem_of_ncard_lt_ncard
  rw[Set.ncard_univ,Nat.card_eq_fintype_card,hG,Set.ncard_eq_toFinset_card']
  simp
  apply lt_of_le_of_lt h1 (by simp)
  exact Set.toFinite {1, a, b, a * b}


/-- A group of order 8 where every non-identity element has order 2 is isomorphic to (the multiplicative version of) `ZMod 2 × ZMod 2 × ZMod 2` -/
lemma zmod2_zmod2_zmod2_of_elts_order_two {G : Type*}[h0: Group G][Fintype G](hG: Fintype.card G = 8)(h1: ∀ g:G, g ≠ 1 → orderOf g = 2): Nonempty (G ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)):= by {
  have hcomm: IsCommutative G (fun x y ↦ x*y):= comm_of_elts_order_two h1
  obtain ⟨a,b,hab,ha1,hb1⟩ := two_distinct_elts hG
  have h2: ∀ (g:G), g⁻¹ = g := by
    intro g
    by_cases hg: g = 1
    · simp[hg]
    · refine mul_eq_one_iff_inv_eq.mp ?_; rw[← pow_two,← h1 g hg];apply pow_orderOf_eq_one g
  obtain ⟨c,hc⟩ := third_distinct_elt hG hab ha1 hb1
  let f1 (g:G) := fun (x:Multiplicative (ZMod 2)) ↦ g ^ x.val
  have hf1mul: ∀ (g:G), ∀ (x y : ZMod 2), f1 g (x + y) = f1 g x * f1 g y:= by
    intro g x y
    simp
    by_cases hg: g =1
    · simp[hg]
    rw[← pow_add,pow_eq_pow_zmod (h1 g hg) (ZMod.val x + ZMod.val y),zmod_two_val_add_eq x y]
    simp
  let f2 (g:G): (Multiplicative (ZMod 2) →* G) := {
    toFun := f1 g
    map_mul' := by exact fun x y ↦ hf1mul g x y
    map_one' := by exact pow_eq_one_iff_modEq.mpr rfl
  }
  have hf2 (g:G): g ≠ 1 →  Injective (f2 g):= by
    intro hg
    rw[injective_iff_map_eq_one]
    intro x
    match x with
    | ((0:ZMod 2) : Multiplicative (ZMod 2)) => simp; rfl
    | ((1:ZMod 2) : Multiplicative (ZMod 2)) => simp; intro hg1; contradiction
  let G1: CommGroup G := {h0 with mul_comm := by exact hcomm.comm}
  let f:= MonoidHom.coprod (f2 a) (MonoidHom.coprod (f2 b) (f2 c))
  have hc1 : c ≠ 1   := by aesop
  have hbc : b ≠ c   := by aesop
  have hca : c ≠ a   := by aesop
  have hcab: c ≠ a*b := by aesop
  have hf2range (g:G): ((f2 g).range:Set G) = {1,g}:= by
    ext x
    constructor
    · simp
      intro y hxy
      match y with
      | ((0:ZMod 2): Multiplicative (ZMod 2)) => simp at hxy; simp[hxy]
      | ((1:ZMod 2): Multiplicative (ZMod 2)) => simp at hxy; group at hxy; simp[hxy]
    · simp
      intro hx
      obtain hx|hx := hx
      · use ((0:ZMod 2): Multiplicative (ZMod 2)); simp[hx]
      · use ((1:ZMod 2): Multiplicative (ZMod 2)); simp[hx]
  have hfbc : (MonoidHom.range (f2 b)) ⊓ (MonoidHom.range (f2 c)) = ⊥ := by
    rw[← Subgroup.coe_eq_singleton]; use 1; aesop
  have hfbcinj: Injective (MonoidHom.coprod (f2 b) (f2 c)):= by
    apply monoid_hom_coprod_injective_of_injective (f2 b) (hf2 b hb1) (f2 c) (hf2 c hc1) hfbc
  have hfabc : ((f2 a).range) ⊓ (MonoidHom.coprod (f2 b) (f2 c)).range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1,hx2⟩ := hx
    have hx3: x ∈ (MonoidHom.range (f2 a):Set G) := by exact hx1
    rw[hf2range a] at hx3
    simp at hx3
    obtain hx3|hx3 := hx3
    · exact hx3
    · simp at hx2
      obtain ⟨y,z,hyz⟩ := hx2
      match y with
      | ((0:ZMod 2): Multiplicative (ZMod 2)) =>
            match z with
            | ((0:ZMod 2): Multiplicative (ZMod 2)) => simp at hyz;exact hyz.symm
            | ((1:ZMod 2): Multiplicative (ZMod 2)) =>
                              rw[hx3,one_zmod2_eq_one] at hyz
                              simp at hyz; contradiction
      | ((1:ZMod 2): Multiplicative (ZMod 2)) =>
             match z with
            | ((0:ZMod 2): Multiplicative (ZMod 2)) => simp[one_zmod2_eq_one] at hyz;rw[hx3] at hyz; rw[hyz] at hab;contradiction
            | ((1:ZMod 2): Multiplicative (ZMod 2)) =>
                              simp[one_zmod2_eq_one,hx3] at hyz
                              have hcab1: c = a*b:= by
                                calc
                                c = b⁻¹ *( b* c):= by group
                                _= b * a:= by rw[h2 b,hyz]
                                _= a* b:= by rw[hcomm.comm a b]
                              contradiction
  have hfinj: Injective  f:= by
    apply monoid_hom_coprod_injective_of_injective (f2 a) (hf2 a ha1) (MonoidHom.coprod (f2 b) (f2 c)) (hfbcinj) hfabc
  apply groups_isom_of_injective_hom hG (by simp) f hfinj
}


/-- Every non-identity element of a group of order 8 has order 2, 4 or 8 -/
lemma elt_order_in_group_eight{G : Type*}[Group G][Fintype G](hG: Fintype.card G = 8) : ∀ (g : G), g ≠ 1 → orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 8:= by
  intro g hg
  have h1: orderOf g ∣ 2^3 := by norm_num; simp[← hG, orderOf_dvd_card_univ]
  rw[dvd_prime_pow (Nat.prime_iff.1 Nat.prime_two)] at h1
  obtain ⟨k,hk1,hk2⟩ := h1
  obtain ⟨u,hg1⟩ := hk2
  simp[Nat.units_eq_one] at hg1
  interval_cases k
  · simp at hg1
    contradiction
  repeat simp[hg1]


/-- If `H` is a subgroup of `G` of index 2 and `g ∉ H`, then `gH = G\H` -/
lemma leftCoset_eq_compl_of_index_two{G : Type*}[Group G](H:Subgroup G)(g:G): Subgroup.index H = 2 → g ∉ H →  leftCoset g H = (Set.univ:Set G)\(H:Set G):= by
  intro h hg
  ext x
  constructor
  · intro hx
    simp
    obtain ⟨y,hy1,hy2⟩ := hx
    simp at hy2
    by_contra hx
    have hg1: g = x* y⁻¹ := by rw[← hy2]; group
    have hg2: g ∈ H:= by
      rw[hg1]
      apply mul_mem hx
      exact Subgroup.inv_mem H hy1
    contradiction
  · simp
    intro hx
    by_contra hx1
    have h1: leftCoset g H = leftCoset x H := by simp[h,hg,hx,leftCoset_eq_iff, Subgroup.mul_mem_iff_of_index_two, Subgroup.inv_mem_iff]
    rw[h1, mem_leftCoset_iff] at hx1
    simp at hx1
    have: 1 ∈ H := by apply one_mem
    contradiction


/-- If `H` is a subgroup of `G` of index 2 and `g ∉ H`, then `Hg = G\H` -/
lemma rightCoset_eq_compl_of_index_two{G : Type*}[Group G](H:Subgroup G)(g:G): Subgroup.index H = 2 → g ∉ H →  rightCoset H g = (Set.univ:Set G)\(H:Set G):= by
  intro h hg
  ext x
  constructor
  · intro hx
    simp
    obtain ⟨y,hy1,hy2⟩ := hx
    simp at hy2
    by_contra hx
    have hg1: g =  y⁻¹ *x := by rw[← hy2]; group
    have hg2: g ∈ H:= by
      rw[hg1]
      apply mul_mem _ hx
      exact Subgroup.inv_mem H hy1
    contradiction
  · simp
    intro hx
    by_contra hx1
    have h1: rightCoset H g = rightCoset H x := by simp [h,hg,hx,rightCoset_eq_iff, Subgroup.mul_mem_iff_of_index_two, Subgroup.inv_mem_iff]
    rw[h1, mem_rightCoset_iff] at hx1
    simp at hx1
    have: 1 ∈ H := by apply one_mem
    contradiction


/-- Any subgroup of index two is normal -/
lemma normal_of_index_two{G : Type*}[Group G](H:Subgroup G): Subgroup.index H = 2 → Subgroup.Normal H := by
  rw [normal_iff_eq_cosets]
  intro h g
  by_cases hg: g ∈ H
  · rw [leftCoset_mem_leftCoset H hg,rightCoset_mem_rightCoset H hg]
  · obtain h1 := leftCoset_eq_compl_of_index_two H g h hg
    obtain h2 := rightCoset_eq_compl_of_index_two H g h hg
    simp[h1,h2]


/-- If G is a finite group and g ∈ G with the order of g smaller than the cardinality of G, then the complement of the subgroup generated by g is nonempty -/
lemma compl_nonmepty_of_orderOf_lt_card{G : Type*}[Group G][Fintype G](g:G): orderOf g < Fintype.card G → Set.Nonempty (Set.univ \ (Subgroup.zpowers g):Set G) := by
  intro hg
  let H := Subgroup.zpowers g
  have hH: Set.ncard (H:Set G)  = orderOf g:= by
    rw[order_eq_card_zpowers' g]
    exact (Set.Nat.card_coe_set_eq (H:Set G)).symm
  have hG: Set.ncard (Set.univ:Set G) = Fintype.card G := by rw[← Nat.card_eq_fintype_card,Set.ncard_univ G]
  have h1: Set.ncard (H:Set G) < Set.ncard (Set.univ:Set G):= by simp[hg,hH,hG]
  exact Set.diff_nonempty_of_ncard_lt_ncard h1


lemma false_of_orderOf_a_eq_orderOf_b_squared{G : Type*}[Group G][Fintype G](hG: Fintype.card G = 8){a b : G}(ha:orderOf a = 4)(hb: b ≠ 1)(h: ∀ (g : G), orderOf g ≠ 8)(hab:orderOf a = orderOf (b^2)): False:= by
  rw[ha,orderOf_pow] at hab
  obtain hb1|hb1|hb1:= elt_order_in_group_eight hG b hb
  repeat
    rw[hb1] at hab; contradiction
  specialize h b; contradiction


/-- If G is a group, a∈G such that <a> has index 2 and b ∈ G∖ <a>, then G = <a,b> -/
lemma closure_ab_eq_univ{G: Type*}[Group G]{a b : G}(hA: Subgroup.index (Subgroup.zpowers a) = 2) (hb: b ∈ (Set.univ:Set G)\(Subgroup.zpowers a: Set G)): (Subgroup.closure {a,b}:Set G) = (Set.univ:Set G) := by
  let A := Subgroup.zpowers a
  apply subset_antisymm
  · simp
  · have h1: (Set.univ: Set G) = (A:Set G) ∪ (Set.univ:Set G)\(A:Set G):= by simp
    rw[h1,Set.union_subset_iff]
    have hab: {a,b} ⊆ (Subgroup.closure {a,b}:Set G):= by exact Subgroup.subset_closure
    constructor
    · simp
      apply Set.mem_of_mem_of_subset _ hab
      exact Set.mem_insert a {b}
    · intro x hx
      simp at hb
      obtain hx1:=leftCoset_eq_compl_of_index_two A b hA hb
      rw[← hx1] at hx
      obtain ⟨c,hc1,hc2⟩ := hx
      simp at hc2
      rw[← hc2]
      have hb1: b ∈ (Subgroup.closure {a,b}:Set G) := by
        apply Set.mem_of_mem_of_subset _ hab
        apply Set.mem_insert_of_mem a rfl
      have ha: (Subgroup.closure {a} : Set G) ⊆ (Subgroup.closure {a,b}:Set G) := by
        simp
        apply hab
        exact Set.mem_insert a {b}
      have hc3: c ∈ (Subgroup.closure {a,b}:Set G) := by
        obtain ⟨k, hk⟩ := hc1
        simp at hk
        rw[← hk]
        apply Set.mem_of_mem_of_subset _ ha
        simp [Subgroup.mem_closure_singleton]
      apply mul_mem hb1 hc3


lemma zmod4_zmod2{G : Type*}[hG0: Group G][Fintype G](hG: Fintype.card G = 8)(hcomm: IsCommutative G (fun x y ↦ x*y)){a b : G}(ha1: orderOf a = 4)(hb1: b ≠ 1)(hb2: b^2 = 1)(hb3: b∉ Subgroup.zpowers a): Nonempty (G ≃* Multiplicative (ZMod 4) × Multiplicative ( ZMod 2)):= by
  let f1 := fun (x:Multiplicative (ZMod 2)) ↦ b^(x.val)
  have hf1mul: ∀ (x y : ZMod 2 ), f1 (x + y) = f1  x * f1 y:= by
    intro x y
    simp
    have hb3: orderOf b = 2:= by exact orderOf_eq_prime hb2 hb1
    rw[← pow_add,pow_eq_pow_zmod hb3 ((ZMod.val x + ZMod.val y))]
    rw[zmod_two_val_add_eq x y]
    simp
  let f2: (Multiplicative (ZMod 2) →* G) := {
    toFun := f1
    map_mul' := by exact fun x y ↦ hf1mul x y
    map_one' := by exact pow_eq_one_iff_modEq.mpr rfl
  }
  have hf2:  Injective f2:= by
    rw[injective_iff_map_eq_one]
    intro x
    match x with
    | ((0:ZMod 2) : Multiplicative (ZMod 2)) => simp; rfl
    | ((1:ZMod 2) : Multiplicative (ZMod 2)) => simp; intro hb4; contradiction
  let hG1: CommGroup G := {hG0 with mul_comm := by exact hcomm.comm}
  let f3 := fun (x:Multiplicative (ZMod 4)) ↦ a^(x.val)
  have hf3mul: ∀ (x y : ZMod 4 ), f3 (x + y) = f3  x * f3 y:= by
    intro x y
    simp
    rw[← pow_add,pow_eq_pow_zmod ha1 ((ZMod.val x + ZMod.val y))]
    rw[zmod_four_val_add_eq x y]
    simp
  let f4: (Multiplicative (ZMod 4) →* G) := {
    toFun := f3
    map_mul' := by exact fun x y ↦ hf3mul x y
    map_one' := by exact pow_eq_one_iff_modEq.mpr rfl
  }
  have hf4: Injective f4:= by
    intro x y hxy
    simp at hxy
    apply zmod_four_eq_of_eq_pow ha1 x y hxy
  let f:= MonoidHom.coprod f4 f2
  have hf2range: (f2.range:Set G) = {1,b}:= by
    ext x
    constructor
    · simp
      intro y hxy
      match y with
      | ((0:ZMod 2): Multiplicative (ZMod 2)) => simp at hxy;simp[hxy]
      | ((1:ZMod 2): Multiplicative (ZMod 2)) => simp at hxy; group at hxy; simp[hxy]
    · simp
      intro hx
      obtain hx|hx := hx
      · use ((0:ZMod 2): Multiplicative (ZMod 2));simp[hx]
      · use ((1:ZMod 2): Multiplicative (ZMod 2));simp[hx]
  have hf4range: (f4.range:Set G) = {1,a,a^2,a^3}:= by
    ext x
    simp
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := hx
      match y with
      | (0:ZMod 4) => simp at hy;simp[hy]
      | (1:ZMod 4) => simp at hy;simp[hy]
      | (2:ZMod 4) => simp at hy;simp[hy]
      | (3:ZMod 4) => simp at hy;simp[hy]
    · intro hx
      obtain hx|hx|hx|hx := hx
      · use (0:ZMod 4);simp[hx]
      · use (1:ZMod 4);simp[hx]
      · use (2:ZMod 4);simp[hx]
      · use (3:ZMod 4);simp[hx]
  have hf : f4.range ⊓ f2.range = ⊥ := by
    rw[← Subgroup.coe_eq_singleton]
    use 1
    aesop
  have hfinj: Injective (MonoidHom.coprod f4 f2):= by
    apply monoid_hom_coprod_injective_of_injective f4 hf4 f2 hf2 hf
  apply groups_isom_of_injective_hom hG (by simp) f hfinj


lemma eq_of_eq_pow{G:Type*}[Group G]{a:G}(ha: orderOf a = 4): ∀ (i j :ZMod 4),a ^ i.val = a^j.val → i = j:= by
    intro i j hij
    rw[← zmod_four_val_eq_self i, ← zmod_four_val_eq_self j]
    rw [pow_inj_mod,ha] at hij
    rw [ZMod.nat_cast_eq_nat_cast_iff']
    exact hij

lemma false_of_pow_a_eq_b_pow_a{G:Type*}[Group G]{a b :G}(hb: b ∈ (Set.univ:Set G) \ (Subgroup.zpowers a :Set G))(n m : ℕ): a ^ n = b* a ^m → False:= by
  intro h
  let A:= Subgroup.zpowers a
  have hb1: b ∉ (A:Set G):= by exact Set.not_mem_of_mem_diff hb
  have hb2: b∈ A:= by
    rw[eq_mul_inv_of_mul_eq (id h.symm)]
    apply Subgroup.mul_mem
    · exact Subgroup.npow_mem_zpowers a n
    · apply Subgroup.inv_mem
      apply Subgroup.npow_mem_zpowers a m
  contradiction

lemma a_neg_pow_b_eq_b_a_pow{G:Type*}[Group G]{a b:G}(hab: a ^ 3 = b * a * b⁻¹)(hab1: a⁻¹ * b = b * a)(hab2: a^2 *b = b* a^2):∀ (i:ZMod 4), (a) ^ (-i).val * b = b* a ^ i.val:= by
  intro i
  match i with
    | 0 => simp
    | 1 => simp[hab]
    | 2 => simp; exact hab2
    | 3 =>  simp
            calc
            a* b = a⁻¹ *(a^2*b) := by group
            _= a⁻¹ *(b*a^2) := by rw[hab2]
            _= (a⁻¹ * b) * a^2:= by group
            _= (b * a) * a^2:= by rw[hab1]
            _= b * a^3 := by group


open DihedralGroup

lemma iso_dihedral{G:Type*}[Group G][Fintype G](hG: Fintype.card G = 8){a b:G}(ha:orderOf a = 4)(hb1: orderOf b = 2)(hb2: b ∈ (Set.univ:Set G) \ (Subgroup.zpowers a :Set G))(hab: a ^ 3 = b * a * b⁻¹) : Nonempty (G ≃* DihedralGroup 4) := by
  let f:= fun  (g:DihedralGroup 4 ) ↦  match g with
    | DihedralGroup.r i => a ^ i.val
    | DihedralGroup.sr i => b * a ^ i.val
  have hf1: Injective f := by
    intro x y hxy
    match x with
    | r i =>
      match y with
        | r j =>  simp at hxy; rw[eq_of_eq_pow ha i j hxy]
        | sr j => simp at hxy; simp[false_of_pow_a_eq_b_pow_a hb2 i.val j.val hxy]
    | sr i =>
      match y with
        | r j =>  simp at hxy; simp[false_of_pow_a_eq_b_pow_a hb2 j.val i.val hxy.symm]
        | sr j => simp at hxy;rw[eq_of_eq_pow ha i j hxy]
  have hf2: Bijective f:= by
    apply (Fintype.bijective_iff_injective_and_card f).2
    constructor
    · apply hf1
    · simp[hG]
  have hab1: a ^ 3 *b = b *a := by symm;apply mul_inv_eq_iff_eq_mul.1 hab.symm
  have ha3: a^3 = a⁻¹   := by
    calc
      a^3 = a^4  * a⁻¹ := by group
      _= 1 * a⁻¹  := by rw[← pow_orderOf_eq_one a,← ha]
      _= a⁻¹ := by group
  rw[ha3] at hab1
  have hab2: a^2 *b = b* a^2:= by
    calc
       a^ 2 * b = a^3 * (a⁻¹ *b):= by group
      _= (b*a*b⁻¹) * (b*a):= by rw[hab,hab1]
      _= b* (a * a):= by group
      _= b * a^2 := by rw[← pow_two]
  obtain ha4 := a_neg_pow_b_eq_b_a_pow hab hab1 hab2
  have hb3: b⁻¹ = b:= by rw[← one_mul b⁻¹,← pow_orderOf_eq_one b, hb1];group
  have hf3: ∀ (x y : DihedralGroup 4), f (x * y) = f x *  f y := by
    intro x y
    match x with
      | r i =>
        match y with
          | r j =>  simp
                    rw[(pow_add a i.val j.val).symm]
                    apply zmod_four_pow_val_sum_eq_pow_sum_val ha i j
          | sr j => simp
                    rw[sub_eq_add_neg,zmod_four_pow_val_sum_eq_pow_sum_val ha j (-i),add_comm,pow_add a ((-i).val)  (j.val),← mul_assoc,← ha4 (-i)]
                    simp[mul_assoc]
      | sr i =>
        match y with
          | r j => simp;rw[zmod_four_pow_val_sum_eq_pow_sum_val ha i j];group
          | sr j => simp
                    rw[sub_eq_add_neg,zmod_four_pow_val_sum_eq_pow_sum_val ha j (-i),add_comm,pow_add a ((-i).val)  (j.val),← mul_assoc]
                    simp[mul_left_eq_iff_eq_invOf_mul]
                    rw[← ha4 i]
                    nth_rw 1[← hb3]
                    simp
  let f_equiv_mul: DihedralGroup 4 ≃* G :={ Equiv.ofBijective f hf2 with map_mul' := by exact fun x y ↦ hf3 x y}
  exact Nonempty.intro (id (MulEquiv.symm f_equiv_mul))


lemma iso_quaternion{G:Type*}[Group G][Fintype G](hG: Fintype.card G = 8){a b:G}(ha:orderOf a = 4)(hb1: orderOf b = 4)(hb2: b ∈ (Set.univ:Set G) \ (Subgroup.zpowers a :Set G))(hb3: b^2 = a^2)(hab: a ^ 3 = b * a * b⁻¹) : Nonempty (G ≃* QuaternionGroup 2) := by
  let f:= fun  (g:QuaternionGroup 2 ) ↦  match g with
    | QuaternionGroup.a i => a ^ i.val
    | QuaternionGroup.xa i => b⁻¹ * a ^ i.val
  have hf1: Injective f := by
    intro x y hxy
    match x with
    | QuaternionGroup.a i =>
        match y with
          | QuaternionGroup.a j => simp at hxy;rw[eq_of_eq_pow ha i j hxy]
          | QuaternionGroup.xa j => simp at hxy
                                    have: a ^ ZMod.val j = b * a ^ ZMod.val i := by simp[hxy]
                                    exfalso
                                    apply false_of_pow_a_eq_b_pow_a hb2 j.val i.val this
    | QuaternionGroup.xa i =>
        match y with
          | QuaternionGroup.a j =>  simp at hxy
                                    have: a ^ ZMod.val i = b * a ^ ZMod.val j := by simp[← hxy]
                                    exfalso
                                    apply false_of_pow_a_eq_b_pow_a hb2 i.val j.val this
          | QuaternionGroup.xa j => simp at hxy;rw[eq_of_eq_pow ha i j hxy]
  have hf2: Bijective f:= by
    apply (Fintype.bijective_iff_injective_and_card f).2
    constructor
    · apply hf1
    · simp[hG]
  have hab1: a ^ 3 *b = b *a := by symm;apply mul_inv_eq_iff_eq_mul.1 hab.symm
  have ha3: a^3 = a⁻¹   := by
    calc
      a^3 = a^4  * a⁻¹ := by group
      _= 1 * a⁻¹  := by rw[← pow_orderOf_eq_one a,← ha]
      _= a⁻¹ := by group
  rw[ha3] at hab1
  have hab2: a^2 *b = b* a^2:= by rw[← hb3]; group
  obtain ha4 := a_neg_pow_b_eq_b_a_pow hab hab1 hab2
  have hb4: b^4 = 1:= by rw[← hb1,pow_orderOf_eq_one]
  have hb5: b^2 = b⁻¹ * b⁻¹ := by
    calc
        b^2 = b^4 * b⁻¹ *b⁻¹:= by group
        _= 1* b⁻¹ *b⁻¹ := by rw[hb4]
        _= b⁻¹ *b⁻¹ := by group
  have hf3: ∀ (x y : QuaternionGroup 2), f (x * y) = f x *  f y := by
    intro x y
    match x with
      | QuaternionGroup.a i =>
        match y with
          | QuaternionGroup.a j =>
                    simp
                    rw[(pow_add a i.val j.val).symm]
                    apply zmod_four_pow_val_sum_eq_pow_sum_val ha i j
          | QuaternionGroup.xa j =>
                    simp
                    rw[sub_eq_add_neg,zmod_four_pow_val_sum_eq_pow_sum_val ha j (-i),add_comm,pow_add a ((-i).val)  (j.val)]
                    rw[inv_mul_eq_iff_eq_mul,← mul_assoc,←  ha4 i]
                    simp[mul_assoc]
      | QuaternionGroup.xa i =>
        match y with
          | QuaternionGroup.a j => simp;rw[zmod_four_pow_val_sum_eq_pow_sum_val ha i j];group
          | QuaternionGroup.xa j =>
                    simp
                    rw[sub_eq_add_neg,add_comm,← add_assoc]
                    rw[zmod_four_pow_val_sum_eq_pow_sum_val ha (-i + 2) j,pow_add]
                    have: b⁻¹ * a ^ ZMod.val i * (b⁻¹ * a ^ ZMod.val j) = b⁻¹ * a ^ ZMod.val i * b⁻¹ * a ^ ZMod.val j := by simp[mul_assoc]
                    rw[this]
                    have:a ^ ZMod.val (-i + 2) * a ^ ZMod.val j = b⁻¹ * a ^ ZMod.val i * b⁻¹ * a ^ ZMod.val j ↔ a ^ ZMod.val (-i + 2)  = b⁻¹ * a ^ ZMod.val i * b⁻¹ := by exact mul_left_inj (a ^ ZMod.val j)
                    rw[this]
                    rw[zmod_four_pow_val_sum_eq_pow_sum_val ha (-i) 2,pow_add]
                    simp
                    match i with
                      | (0:ZMod 4) => rw[← hb3]; simp; exact hb5
                      | (1:ZMod 4) =>
                              simp
                              calc
                                a^3 * a^2 = a^ 2 * a^ 3:= by group
                                _= b^2 * (b * a* b⁻¹) := by rw[hb3.symm, hab]
                                _= b⁻¹ * b⁻¹ * (b * a* b⁻¹) := by rw[hb5]
                                _= b⁻¹ * a * b⁻¹ := by group
                      | (2:ZMod 4) =>
                              rw[neg_two_zmod4_eq_two]
                              simp[← hb3]
                              group
                              rw[← hb4]
                              norm_cast
                      | (3:ZMod 4) =>
                              rw[neg_three_zmod4_eq_one]
                              simp[hab,← hb3, hb5]
                              group
  let f_equiv_mul: QuaternionGroup 2 ≃* G :={ Equiv.ofBijective f hf2 with map_mul' := by exact fun x y ↦ hf3 x y}
  exact Nonempty.intro (id (MulEquiv.symm f_equiv_mul))


lemma b_squared_in_zpowers_a{G : Type*}[Group G]{a b: G}(hA2: Subgroup.index (Subgroup.zpowers a) = 2)(hbA: b∉ ((Subgroup.zpowers a):Set G)): b^2 ∈ (Subgroup.zpowers a):= by
  let A:= Subgroup.zpowers a
  by_contra hcon
  obtain hb1:= leftCoset_eq_compl_of_index_two A (b^2) hA2 hcon
  obtain hb2:= leftCoset_eq_compl_of_index_two A (b) hA2 hbA
  rw[← hb2,leftCoset_eq_iff] at hb1
  group at hb1
  rw [zpow_neg_one,Subgroup.inv_mem_iff] at hb1
  contradiction

lemma b_squared_eq_one_or_a_squared{G : Type*}[Group G][Fintype G](hG: Fintype.card G = 8)(h3: ∀ (g : G), orderOf g ≠ 8){a b:G}(ha3: orderOf a = 4)(hb1: b ≠ 1){k:ℤ}(hk:a ^ (k % ↑4) = b ^ 2):b^2 = 1 ∨ b ^ 2 = a^2 := by
  have hk1: 0 ≤ k%4 := by apply Int.emod_nonneg; simp
  have hk2: k%4 < 4 := by apply Int.emod_lt_of_pos; simp
  interval_cases k%4
  · simp at hk
    simp[hk]
  · simp at hk
    have h6: orderOf a = orderOf (b^2):= by exact congrArg orderOf hk
    exfalso
    apply false_of_orderOf_a_eq_orderOf_b_squared hG ha3 hb1 h3 h6
  · have: a^2 = a^(2:ℤ):= by rw[pow_two,zpow_two]
    rw[this,hk]
    simp
  · have ha5: a^(3:ℤ) = a ^ 4 * a⁻¹ := by group
    rw[ha5,← ha3,pow_orderOf_eq_one a, one_mul] at hk
    have h6: orderOf a⁻¹  = orderOf (b^2):= by exact congrArg orderOf hk
    rw [orderOf_inv] at h6
    exfalso
    apply false_of_orderOf_a_eq_orderOf_b_squared hG ha3 hb1 h3 h6

lemma square_b_inv_a_eq_one_of_a_sq_eq_b_sq{G : Type*}[Group G](hcomm: IsCommutative G (fun x y ↦ x*y) )(a b:G)(hb2: b ^ 2 = a ^ 2): (b*a⁻¹)^2 = 1:= by
  calc
    (b*a⁻¹ )^2 = (b*(a⁻¹  *b)*a⁻¹ ) := by simp[pow_two,mul_assoc]
    _= (b*(b* a⁻¹ )*a⁻¹ ) := by simp[hcomm.comm]
    _= b*b*(a⁻¹ * a⁻¹) := by group
    _= b^2 * (a⁻¹ * a⁻¹) := by simp[pow_two]
    _= a^2 * (a⁻¹ * a⁻¹) := by rw[hb2]
    _= 1:= by group

lemma neq_one_of_not_mem_subgroup{G: Type*}[Group G]{H: Subgroup G}{g: G}(hg: g ∉ H): g ≠ (1:G):= by
  by_contra hcon
  rw[hcon] at hg
  have hA5: 1 ∈ H := by exact Subgroup.one_mem H
  contradiction

lemma orderOf_b_eq_four{G: Type*}[Group G][Fintype G](hG: Fintype.card G = 8)(h1: ∀ (g : G), orderOf g ≠ 8){a b:G}(ha: orderOf a = 4)(hb1: b ≠ 1)(hb2: b ^ 2 = a ^ 2): orderOf b = 4 := by
  obtain hb4 := elt_order_in_group_eight hG b hb1
  simp[h1] at hb4
  obtain hb4|hb4 := hb4
  · nth_rw 1 [← hb4] at hb2
    rw [pow_orderOf_eq_one] at hb2
    have: orderOf a ∣ 2:= by exact orderOf_dvd_of_pow_eq_one (id hb2.symm)
    rw[ha] at this
    simp at this
  · exact hb4

/-- Every group of order 8 is isomorphic to one of `ZMod 8`, `(ZMod 4) × (ZMod 2)`, `ZMod 2 × ZMod 2 × ZMod 2`, `DihedralGroup 4`, `QuaternionGroup 2`.   -/
lemma groups_order_eight {G : Type*}[Group G][Fintype G](hG: Fintype.card G = 8):
    Nonempty (G ≃* Multiplicative (ZMod 8))
    ∨ Nonempty (G ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2))
    ∨ Nonempty (G ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    ∨ Nonempty (G ≃* DihedralGroup 4)
    ∨ Nonempty (G ≃* QuaternionGroup 2) :=  by
      by_cases h1: ∃ (g:G), orderOf g = 8
      · obtain ⟨g, hg⟩ := h1
        simp[zmod8_of_elt_order_eight hG hg]
      push_neg at h1
      by_cases h2: ∀ (g:G), g ≠ 1 → orderOf g = 2
      · simp[zmod2_zmod2_zmod2_of_elts_order_two hG h2]
      push_neg at h2
      obtain ⟨a,ha1, ha2⟩ := h2
      have ha3: orderOf a = 4:= by
        obtain h:= elt_order_in_group_eight hG a ha1
        simp[ha2, h1 a] at h
        exact h
      let A := Subgroup.zpowers a
      have hA1: Fintype.card (A) = 4 := by rw [← ha3, ← Nat.card_eq_fintype_card]; exact (order_eq_card_zpowers' a).symm
      obtain ⟨b,hb⟩  := compl_nonmepty_of_orderOf_lt_card a (by simp[hG,ha3])
      have hbA: b ∉ (A:Set G):= by exact Set.not_mem_of_mem_diff hb
      have hA2: Subgroup.index A = 2:= by
        have: Subgroup.index A * 4 = 8:= by
          rw[← hG, ← hA1]
          apply Subgroup.index_mul_card
        linarith
      have hA3: Subgroup.Normal A := normal_of_index_two A hA2
      have hb0: b^2 ∈ A:= by apply b_squared_in_zpowers_a hA2 hbA
      obtain ⟨k0,hk0⟩ := hb0
      simp at hk0
      rw[zpow_eq_mod_orderOf,ha3] at hk0
      have hb1: b ≠ 1:= by apply neq_one_of_not_mem_subgroup hbA
      have hb2: b^2 = 1 ∨ b ^ 2 = a^2 := by apply b_squared_eq_one_or_a_squared hG h1 ha3 hb1 hk0
      have ha4: b*a*b⁻¹ ∈ A := Subgroup.Normal.conj_mem hA3 a (Subgroup.mem_zpowers a) b
      obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.1 ha4
      have ha5: a ^ (k%4) = b* a * b⁻¹ := by
        rw [← hk];
        refine zpow_eq_zpow_iff_modEq.mpr ?_
        rw[ha3]
        exact Int.mod_modEq k 4
      have hk1: 0 ≤ k%4 := by apply Int.emod_nonneg; simp
      have hk2: k%4 < 4 := by apply Int.emod_lt_of_pos; simp
      interval_cases k%4
      · simp[eq_mul_inv_iff_mul_eq,one_mul,self_eq_mul_right] at ha5
        simp[ha5] at ha3
      · simp at ha5
        rw [eq_mul_inv_iff_mul_eq] at ha5
        have hab: ∀ x ∈ ({a,b}:Set G), ∀ y ∈ ({a,b}:Set G), x*y = y*x:= by simp[ha5]
        have hab1: IsCommutative (Subgroup.closure ({a,b})) (fun x y ↦ x*y) := by
          let hcomm: CommGroup (Subgroup.closure ({a,b}:Set G)):= by apply Subgroup.closureCommGroupOfComm hab
          apply CommSemigroup.to_isCommutative
        have hab2 (x y: Subgroup.closure {a,b}): x*y = y*x := by apply hab1.comm
        have hab3: Subgroup.closure {a,b} = ⊤ := by exact Subgroup.coe_eq_univ.mp (closure_ab_eq_univ hA2 hb)
        have h3 (x:G): x ∈ Subgroup.closure {a,b}:= by simp[hab3]
        have h4 (x y:G): x*y = y*x := by
          specialize hab2 ⟨x, h3 x⟩ ⟨y, h3 y⟩
          simp at hab2
          exact hab2
        have hcomm: IsCommutative G (fun x y ↦ x*y) := by exact { comm := h4 }
        obtain hb2|hb2:= hb2
        · simp[zmod4_zmod2 hG hcomm ha3 hb1 hb2 hbA]
        · let c := b*a⁻¹
          have hcA: c ∉ A:= by
            by_contra hcon
            have h7: b* a⁻¹ * a∈ A:= by exact Subgroup.mul_mem A hcon (Subgroup.mem_zpowers a)
            simp at h7
            contradiction
          have hc1: c ≠ 1:= by apply neq_one_of_not_mem_subgroup hcA
          have hc2: c^2 = 1:= by apply square_b_inv_a_eq_one_of_a_sq_eq_b_sq hcomm a b hb2
          simp[zmod4_zmod2 hG hcomm ha3 hc1 hc2 hcA]
      · have ha6: a^4 =1 :=by rw[← ha3]; exact pow_orderOf_eq_one a
        have ha7: (orderOf a) ∣ 2 := by
          apply orderOf_dvd_of_pow_eq_one
          calc
            a^2 = b⁻¹ *(b*a*b⁻¹)*(b*a*b⁻¹) *b := by rw[pow_two];group
            _= b⁻¹ * ((a^2) * (a^2)) * b:= by rw [← ha5];group
            _= 1 := by rw[← pow_add a 2 2,ha6];group
        rw[ha3] at ha7
        contradiction
      · norm_cast at ha5
        obtain hb2|hb2:= hb2
        · have hb3: orderOf b = 2:= by exact orderOf_eq_prime hb2 hb1
          simp[iso_dihedral hG ha3 hb3 hb ha5]
        · have hb3: orderOf b = 4:= by apply orderOf_b_eq_four hG h1 ha3 hb1 hb2
          simp[iso_quaternion hG ha3 hb3 hb hb2 ha5]

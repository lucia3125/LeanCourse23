import LeanCourse.Common
import Mathlib.GroupTheory.FiniteAbelian
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.Coset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

open BigOperators

/-- Every abelian group, considered as additive, of order 8 is isomorphic to one of `ZMod 8`, `(ZMod 4) × (ZMod 2)`, `ZMod 2 × ZMod 2 × ZMod 2`. -/
lemma add_comm_groups_order_eight (G : Type*) [AddCommGroup G](h1: Fintype G)(h2: Fintype.card G = 8): Nonempty (G ≃+ (ZMod 8)) ∨ Nonempty ( G ≃+ ((ZMod 4) ×  (ZMod 2))) ∨ Nonempty (G ≃+ (ZMod 2 × ZMod 2 × ZMod 2))  :=  by
  obtain ⟨ι, fι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_fintype G
  have h3 (n:ℕ )(hn: n≠ 0): Fintype (ZMod n):= by
    have: NeZero n := by exact { out := hn }
    apply ZMod.fintype n
  have h4 (i:ι): Fintype (ZMod (p i ^ e i)):= by
    apply h3
    have hnonzero: p i ≠ 0 := by exact Nat.Prime.ne_zero (hp i)
    exact pow_ne_zero (e i) hnonzero
  let h5: Fintype (⨁ (i : ι), ZMod (p i ^ e i)) := by apply Fintype.ofEquiv _ f.toEquiv
  have h6: 8= Fintype.card (⨁ (i : ι), ZMod (p i ^ e i)) := by rw[← h2]; exact (Fintype.ofEquiv_card f.toEquiv).symm
  have h7:  Fintype.card (⨁ (i : ι), ZMod (p i ^ e i)) =  (∏ i,  Fintype.card (ZMod (p i ^ e i)) ):= by
    sorry
  sorry


/-- For a multiplicative group G and additive group H, (G,*) and (H,*) are isomorphic if and only if (G,+) and (H,+) are isomorphic -/
lemma additive_multiplicative_iso {G H: Type*} [Group G][AddCommGroup H]: Nonempty (G ≃* Multiplicative H) ↔ Nonempty (Additive G ≃+ H) := by
  have h:(G ≃* Multiplicative H)  ≃  (Additive G ≃+ H) := MulEquiv.toAdditive'
  exact Equiv.nonempty_congr h


/-- Conversion from additive to multiplicative notation -/
lemma comm_groups_order_eight {G : Type*} [hG: Group G](h1: Fintype G)(h2: Fintype.card G = 8)(h3: IsCommutative G fun x y ↦ x*y): Nonempty (G ≃* Multiplicative (ZMod 8)) ∨ Nonempty (G ≃* Multiplicative ((ZMod 4) ×  (ZMod 2))) ∨ Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2))  :=  by
  let G1: AddCommGroup (Additive G) := {hG with add_comm := by exact h3.comm}
  simp[additive_multiplicative_iso]
  exact add_comm_groups_order_eight (Additive G) h1 h2


/-- If a group of order 8 has an element of order 8, it is abelian -/
lemma comm_of_elt_order_eight{G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8)(g:G)(hg: orderOf g = 8): IsCommutative G (fun x y ↦ x*y):= by
  have hg1: orderOf g = Fintype.card G:= by simp[h2,hg]
  have hG: IsCyclic G:= isCyclic_of_orderOf_eq_card g hg1
  let hcomm: CommGroup G:= IsCyclic.commGroup
  exact CommSemigroup.to_isCommutative


/-- A group where every non-identity element has order 2 is abelian -/
lemma comm_of_elts_order_two {G : Type*}[Group G](h: ∀ g:G, g ≠ 1 → orderOf g = 2): IsCommutative G (fun x y ↦ x*y) where
  comm := by
    intro a b
    have h1: ∀ g:G, g*g = 1 := by{
      intro g
      by_cases hg: g = 1
      · simp[hg]
      · specialize h g hg
        rw [← pow_two, ← h, pow_orderOf_eq_one]
    }
    calc
      a * b = (a * b) * (a * b) * b⁻¹ * a⁻¹ := by group
      _ = 1 * b⁻¹ * (b*b) * a⁻¹ * (a*a) := by rw[h1 (a*b), h1 b, h1 a]; group
      _ = b * a := by group


/-- Every non-identity element of a group of order 8 has order 2, 4 or 8 -/
lemma elt_order_in_group_eight{G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8) : ∀ (g : G), g ≠ 1 → orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 8:= by
  intro g hg
  have h3: orderOf g ∣ 2^3 := by norm_num; simp[← h2, orderOf_dvd_card_univ]
  rw[dvd_prime_pow (Nat.prime_iff.1 Nat.prime_two)] at h3
  obtain ⟨k,hk1,hk2⟩ := h3
  obtain ⟨u,hg1⟩ := hk2
  simp[Nat.units_eq_one] at hg1
  interval_cases k
  · simp at hg1
    contradiction
  repeat simp[hg1]


/-- A non-abelian group of order 8 has an element of order 4 -/
lemma elt_order_four_of_noncomm{G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8) : (¬ (IsCommutative G (fun x y ↦ x*y)) ) → ∃ g:G, orderOf g = 4:= by {
  intro hnoncomm
  by_contra hcon
  push_neg at hcon
  have h3: ∀ (g : G), g ≠ 1 → orderOf g = 2 := by
    intro g hg
    specialize hcon g
    obtain h4|h4|h4 := elt_order_in_group_eight h1 h2 g hg
    · exact h4
    · contradiction
    · have hcomm: IsCommutative G (fun x y ↦ x*y) := comm_of_elt_order_eight h1 h2 g h4
      contradiction
  obtain hcomm := comm_of_elts_order_two h3
  contradiction
}


/-- If H is a subgroup of G of index 2 and g ∉ H, then gH = G\H -/
lemma leftCoset_eq_compl_of_index_two(G : Type*) [Group G](H:Subgroup G)(g:G): Subgroup.index H = 2 → g ∉ H →  leftCoset g H = (Set.univ:Set G)\(H:Set G):= by
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
    have h1: leftCoset g H = leftCoset x H := by simp [h,hg,hx,leftCoset_eq_iff, Subgroup.mul_mem_iff_of_index_two, Subgroup.inv_mem_iff]
    rw[h1, mem_leftCoset_iff] at hx1
    simp at hx1
    have: 1 ∈ H := by apply one_mem
    contradiction


/-- If H is a subgroup of G of index 2 and g ∉ H, then Hg = G\H -/
lemma rightCoset_eq_compl_of_index_two(G : Type*) [Group G](H:Subgroup G)(g:G): Subgroup.index H = 2 → g ∉ H →  rightCoset H g = (Set.univ:Set G)\(H:Set G):= by
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
lemma normal_of_index_two{G : Type*} [Group G]{H:Subgroup G}: Subgroup.index H = 2 → Subgroup.Normal H := by
  rw [normal_iff_eq_cosets]
  intro h g
  by_cases hg: g ∈ H
  · rw [leftCoset_mem_leftCoset H hg,rightCoset_mem_rightCoset H hg]
  · obtain h1 := leftCoset_eq_compl_of_index_two G H g h hg
    obtain h2 := rightCoset_eq_compl_of_index_two G H g h hg
    simp[h1,h2]


/-- If G is a finite group and g ∈ G with the order of g smaller than the cardinality of G, then the complement of the subgroup generated by g is nonempty -/
lemma compl_nonmepty_of_orderOf_lt_card{G : Type*} [Group G](h1: Fintype G)(g: G): orderOf g < Fintype.card G → Set.Nonempty (Set.univ \ (Subgroup.zpowers g):Set G) := by
  intro hg
  let H := Subgroup.zpowers g
  have hH: Set.ncard (H:Set G)  = orderOf g:= by
    rw[order_eq_card_zpowers' g]
    exact (Set.Nat.card_coe_set_eq (H:Set G)).symm
  have hG: Set.ncard (Set.univ:Set G) = Fintype.card G := by rw[← Nat.card_eq_fintype_card,Set.ncard_univ G]
  have h2: Set.ncard (H:Set G) < Set.ncard (Set.univ:Set G):= by simp[hg,hH,hG]
  exact Set.diff_nonempty_of_ncard_lt_ncard h2


/-- If G is a group, a∈G such that <a> has index 2 and b ∈ G∖ <a>, then G = <a,b> -/
lemma closure_ab_eq_univ{G: Type*} [Group G](a b : G)(hA: Subgroup.index (Subgroup.zpowers a) = 2) (hb:b∈ (Set.univ:Set G)\(Subgroup.zpowers a: Set G)): (Subgroup.closure {a,b}:Set G) = (Set.univ:Set G) := by
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
      obtain hx1:=leftCoset_eq_compl_of_index_two G A b hA hb
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


/-- Every non-abelian group of order 8 is isomorphic to `DihedralGroup 4` or `QuaternionGroup 2`.   -/
lemma noncomm_groups_order_eight{G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8)(hnoncomm: ¬ (IsCommutative G (fun x y ↦ x*y))): Nonempty (G ≃* (DihedralGroup 4)) ∨ Nonempty (G ≃* (QuaternionGroup 2))  :=  by
  obtain ⟨a,ha⟩ := elt_order_four_of_noncomm h1 h2 hnoncomm
  let A := Subgroup.zpowers a
  have hA1: Fintype.card (A) = 4 := by rw [← ha, ← Nat.card_eq_fintype_card]; exact (order_eq_card_zpowers' a).symm
  have ha1: orderOf a < Fintype.card G := by simp[h2,ha]
  obtain ⟨b,hb⟩  := compl_nonmepty_of_orderOf_lt_card h1 a ha1
  have hA2: Subgroup.index (Subgroup.zpowers a) = 2:= by
    have: Subgroup.index A * 4 = 8:= by
      rw[← h2, ← hA1]
      apply Subgroup.index_mul_card
    linarith
  have hA3: Subgroup.Normal A := normal_of_index_two hA2
  have ha2: a ∈ A := Subgroup.mem_zpowers a
  have ha3: b*a*b⁻¹ ∈ A := Subgroup.Normal.conj_mem hA3 a ha2 b
  obtain ⟨k,hk⟩  := Subgroup.mem_zpowers_iff.1 ha3
  have ha4: a ^ (k%4) = b* a * b⁻¹ := by
    rw [← hk];
    refine zpow_eq_zpow_iff_modEq.mpr ?_
    rw[ha]
    exact Int.mod_modEq k 4
  have hk1: 0 ≤ k%4 := by apply Int.emod_nonneg; simp
  have hk2: k%4 < 4 := by apply Int.emod_lt_of_pos; simp
  interval_cases k%4
  · simp[eq_mul_inv_iff_mul_eq,one_mul,self_eq_mul_right] at ha4
    simp[ha4] at ha
  · simp at ha4
    have hab: ∀ x ∈ ({a,b}:Set G), ∀ y ∈ ({a,b}:Set G), x*y = y*x:= by simp[mul_eq_of_eq_mul_inv ha4]
    have hab1: IsCommutative (Subgroup.closure ({a,b})) (fun x y ↦ x*y) := by
      let hcomm: CommGroup (Subgroup.closure ({a,b}:Set G)):= by apply Subgroup.closureCommGroupOfComm hab
      apply CommSemigroup.to_isCommutative
    have hab2 (x y: Subgroup.closure {a,b}): x*y = y*x := by apply IsCommutative.comm
    obtain  hab3 := closure_ab_eq_univ a b hA2 hb
    have hab4: Subgroup.closure {a,b} = ⊤ := by
      simp[hab3,Subgroup.eq_top_iff']
      intro x
      have: x∈ ((Subgroup.closure {a,b}):Set G):= by simp[hab3]
      exact this
    have h3 (x:G):x∈ Subgroup.closure {a,b}:= by simp[hab4]
    have h4 (x y:G): x*y = y*x := by
      specialize hab2 ⟨x, h3 x⟩ ⟨y, h3 y⟩
      simp at hab2
      exact hab2
    have: IsCommutative G (fun x y ↦ x*y) := by exact { comm := h4 }
    contradiction
  · have ha5:a^4 =1 :=by rw[← ha]; exact pow_orderOf_eq_one a
    have ha6:a^2 = 1:= by
      calc
        a^2 = b⁻¹ *(b*a*b⁻¹)*(b*a*b⁻¹) *b := by rw[pow_two];group
        _= b⁻¹ * ((a^2) * (a^2)) * b:= by rw [← ha4];group
        _= b⁻¹ * 1 * b:= by rw[← pow_add a 2 2,ha5]
        _= 1 := by group
    have ha7: (orderOf a) ∣  2 := by exact orderOf_dvd_of_pow_eq_one ha6
    rw[ha] at ha7
    contradiction
  · have hb1: b ≠ 1:= by
      by_contra hcon
      rw[hcon] at hb
      have hA4: 1 ∉ (A:Set G) := by apply Set.not_mem_of_mem_diff hb
      have hA5: 1 ∈ A := by exact Subgroup.one_mem A
      contradiction
    obtain h3|h3|h3:= elt_order_in_group_eight h1 h2 b hb1
    · -- orderOf b = 2 => DihedralGroup 4
      left
      sorry
    · -- orderOf b = 4 => QuaternionGroup 2
      right
      sorry
    · obtain h23:= comm_of_elt_order_eight h1 h2 b h3
      contradiction


/-- Every group of order 8 is isomorphic to one of `ZMod 8`, `(ZMod 4) × (ZMod 2)`, `ZMod 2 × ZMod 2 × ZMod 2`, `DihedralGroup 4`, `QuaternionGroup 2`.   -/
lemma groups_order_eight {G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8): (Nonempty (G ≃* Multiplicative (ZMod 8)) ∨ Nonempty (G ≃* Multiplicative ((ZMod 4) ×  (ZMod 2))) ∨ Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) ) ∨ Nonempty (G ≃* (DihedralGroup 4)) ∨ Nonempty (G ≃* (QuaternionGroup 2))  :=  by
  by_cases hcomm: IsCommutative G (fun x y ↦ x*y)
  · left
    apply comm_groups_order_eight h1 h2 hcomm
  · right
    apply noncomm_groups_order_eight h1 h2 hcomm




lemma addOrderOf_elt_zmodn_dvd_n(n:ℕ )[NeZero n](a: ZMod n): addOrderOf a ∣ n:= by
  have: Fintype (ZMod n):= by refine ZMod.fintype n
  have ha: addOrderOf a ∣ Fintype.card (ZMod n) := by apply addOrderOf_dvd_card_univ
  simp at ha
  exact ha


/-- If the order of `x.1` divides `n` and the order of `x.2` divides `n`, then order of `x`  divides `n` -/
lemma addOrderOf_prod_dvd{A B: Type*}[AddMonoid A][AddMonoid B](n :ℕ)(x : A × B) (hx1: addOrderOf x.1∣n)(hx2: addOrderOf x.2∣ n): addOrderOf x ∣ n := by
  rw[Prod.add_orderOf x]
  apply lcm_dvd_iff.2
  constructor
  · exact hx1
  · exact hx2


/-- Order of any element in `ZMod 2 × ZMod 2 × ZMod 2` divides 2 -/
lemma addOrderOf_elt_zmod2zmod2zmod2(a: ZMod 2 × ZMod 2 × ZMod 2): addOrderOf a ∣ 2 := by
  repeat
    apply addOrderOf_prod_dvd 2 _ _ _
    apply addOrderOf_elt_zmodn_dvd_n 2 _
  apply addOrderOf_elt_zmodn_dvd_n 2 _


lemma zmod8_not_isom_zmod4zmod2_v2: IsEmpty ( ZMod 8 ≃+ ZMod 4 × ZMod 2 ) := by
  let Z2 :=  (ZMod 2)
  let Z4 :=  (ZMod 4)
  by_contra hcon
  have hnonempty: Nonempty ( ZMod 8 ≃+ ZMod 4 × ZMod 2 ) := by exact not_isEmpty_iff.mp hcon
  obtain ⟨f⟩  := hnonempty
  have ha1 (a:Z4): addOrderOf a ∣ 4 := by apply addOrderOf_elt_zmodn_dvd_n 4 a
  have ha2 (a:Z2): addOrderOf a ∣ 4 := by
    have: 2 ∣ 4:= by simp
    apply dvd_trans (addOrderOf_elt_zmodn_dvd_n 2 a) this
  have ha3 (a: Z4× Z2): addOrderOf a ∣ 4:= by exact addOrderOf_prod_dvd 4 a (ha1 a.1) (ha2 a.2)
  have ha4 (a: Z4 × Z2): 4 • a =0 := by apply addOrderOf_dvd_iff_nsmul_eq_zero.1 (ha3 a)
  have hf1:(f 1 + f 1) = 2 • (f 1):= by rw[← two_smul ℤ (f 1)];rfl
  have hf2: f (1+1) = f 1 + f 1 := by exact AddEquiv.map_add f 1 1
  have hf3: f 4 = 0:= by
    calc
      f 4 = f (2 + 2):= by norm_num
      _= f 2 + f 2:= by exact AddEquiv.map_add f 2 2
      _= f (1+1) + f (1+1) := by norm_num
      _= (f 1 + f 1) +  (f 1 + f 1) := by rw[hf2]
      _= (2 • (f 1) ) + (2 • (f 1)) := by rw[hf1]
      _= 4 • (f 1):= by rw [← add_nsmul]
      _= 0:= by exact ha4 (f 1)
  have h: f.invFun (f (4:ZMod 8)) = f.invFun 0 := by exact congrArg f.invFun hf3
  simp at h


/-- In any monoid isomorphic to `ZMod 2 × ZMod 2 × ZMod 2`, `0 = 2` holds -/
lemma zero_eq_two_of_isom_zmod2zmod2zmod2{A: Type*}[AddMonoidWithOne A](f: A ≃+ ZMod 2 × ZMod 2 × ZMod 2): (0: A) = (2:A) := by
  let Z2:= ZMod 2
  have h1 (a: Z2 × Z2 × Z2): addOrderOf a ∣ 2:= by apply addOrderOf_elt_zmod2zmod2zmod2 a
  have h2 (a: Z2 × Z2 × Z2): 2 • a =0 := by apply addOrderOf_dvd_iff_nsmul_eq_zero.1 (h1 a)
  have h3: (2:A) = 1+1:= by exact one_add_one_eq_two.symm
  have hf1: f 2 = 0:= by
    calc
      f 2 = f (1+1) := by rw[h3]
      _= f 1 + f 1 := by simp
      _= 2 • (f 1) := by rw[← two_smul ℤ (f 1)];rfl
      _= 0 := by exact h2 (f 1)
  have h: f.invFun (f 0) = f.invFun ( f 2) := by rw[f.map_zero,hf1]
  simp at h
  exact h


lemma zmod8_not_isom_zmod2zmod2zmod2: IsEmpty ( ZMod 8 ≃+ ZMod 2 × ZMod 2 × ZMod 2 ) := by
  by_contra hcon
  obtain hnonempty:=  not_isEmpty_iff.mp hcon
  obtain ⟨f⟩ := hnonempty
  have: (0:ZMod 8) = 2:= by apply zero_eq_two_of_isom_zmod2zmod2zmod2 f
  contradiction


lemma zmod4zmod2_not_isom_zmod2zmod2zmod2: IsEmpty ( ZMod 4 × ZMod 2 ≃+ ZMod 2 × ZMod 2 × ZMod 2 ) := by
  by_contra hcon
  obtain hnonempty:= by exact not_isEmpty_iff.mp hcon
  obtain ⟨f⟩ := hnonempty
  have: (0 : ZMod 4 × ZMod 2) = 2:= by apply zero_eq_two_of_isom_zmod2zmod2zmod2 f
  contradiction


/-- Given two elements in a group `G` which do not commute, it follows that there is no isomorphism from `G` to a given commutative group `H` -/
lemma not_isom_comm_of_two_elts_not_comm{G H:Type*}[Group G][AddCommGroup H]{x y:G}(h: x * y ≠ y * x): IsEmpty (G ≃* Multiplicative H ) := by
  by_contra hcon
  obtain hnonempty:= not_isEmpty_iff.mp hcon
  obtain ⟨f⟩  := hnonempty
  have hf1:f (x * y) = f (x) * f (y):= by exact MulEquiv.map_mul f x y
  have hf2: f (y * x) = f (x * y) := by
    calc
      f (y * x) = f (y) * f (x) := by exact MulEquiv.map_mul f y x
      _= f (x) * f (y) := by exact mul_comm (f (y)) (f (x))
      _=  f (x * y) := by rw[← hf1]
  have hf3: f.symm (f (y * x)) = f.symm (f (x * y)) := by rw[hf2]
  simp at hf3
  rw[hf3] at h
  contradiction


/-- `DihedralGroup 4` is not isomorphic to a given commutative group  -/
lemma D4_not_isom_comm{A:Type*}[AddCommGroup A]: IsEmpty (DihedralGroup 4 ≃* Multiplicative A ) := by
  have h: (DihedralGroup.sr 0:DihedralGroup 4) * DihedralGroup.r 1 ≠   DihedralGroup.r 1 * DihedralGroup.sr 0 := by simp
  apply not_isom_comm_of_two_elts_not_comm h

lemma D4_not_isom_zmod8: IsEmpty (DihedralGroup 4 ≃* Multiplicative (ZMod 8) ) := by apply D4_not_isom_comm

lemma D4_not_isom_zmod4zmod2: IsEmpty (DihedralGroup 4 ≃* Multiplicative (ZMod 4 × ZMod 2) ) := by apply D4_not_isom_comm

lemma D4_not_isom_zmod2zmod2zmod2: IsEmpty (DihedralGroup 4 ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) ) := by apply D4_not_isom_comm


/-- `QuaternionGroup 2` is not isomorphic to a given commutative group  -/
lemma Q2_not_isom_comm{A:Type*}[AddCommGroup A]: IsEmpty (QuaternionGroup 2 ≃* Multiplicative A ) := by
  have h:(QuaternionGroup.xa 0 :QuaternionGroup 2)* QuaternionGroup.a 1 ≠  QuaternionGroup.a 1 * QuaternionGroup.xa 0 := by simp
  apply not_isom_comm_of_two_elts_not_comm h

lemma Q2_not_isom_zmod8: IsEmpty (QuaternionGroup 2 ≃* Multiplicative (ZMod 8) ) := by apply Q2_not_isom_comm

lemma Q2_not_isom_zmod4zmod2: IsEmpty (QuaternionGroup 2 ≃* Multiplicative (ZMod 4 × ZMod 2) ) := by apply Q2_not_isom_comm

lemma Q2_not_isom_zmod2zmod2zmod2: IsEmpty (QuaternionGroup 2 ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) ) := by apply Q2_not_isom_comm


/--`DihedralGroup 4` and `QuaternionGroup 2` are not isomorphic-/
lemma D4_not_isom_Q2: IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2) := by
  sorry

import LeanCourse.Common
import Mathlib.Algebra.Module.PID
import Mathlib.Data.ZMod.Quotient
import Mathlib.GroupTheory.FiniteAbelian
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset
import Mathlib.Init.Logic
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.GroupTheory.OrderOfElement


/-- Every abelian group of order 8 is isomorphic to one of `ZMod 8`, `(ZMod 4) × (ZMod 2)`, `ZMod 2 × ZMod 2 × ZMod 2`. -/
lemma comm_groups_order_eight {G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8)(h3: IsCommutative G (fun x y ↦ x*y)): Nonempty (G ≃* (ZMod 8)) ∨ Nonempty (G ≃*((ZMod 4) ×  (ZMod 2))) ∨ Nonempty (G ≃* (ZMod 2 × ZMod 2 × ZMod 2))  :=  by {
  have h4: Finite G := by exact Fintype.finite h1
  -- have h5: ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (e : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) , Nonempty <| G ≃+ ⨁ i : ι, ZMod (p i ^ e i) := by {
  --   -- apply AddCommGroup.equiv_directSum_zmod_of_fintype
  --   sorry
  --   }
  sorry
}


lemma ispgroup_of_card_8 {G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8): IsPGroup 2 G := by
  have hG : Fintype.card G = 2 ^ 3:= by simp[h2]
  apply IsPGroup.of_card hG


/-- If a group of order 8 has an element of order 8, it is abelian -/
lemma comm_of_elt_order_eight{G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8)(g:G)(hg: orderOf g = 8): IsCommutative G (fun x y ↦ x*y):= by{
  have h4: orderOf g = Fintype.card G:= by simp[h2,hg]
  have h5: IsCyclic G:= by apply isCyclic_of_orderOf_eq_card g h4
  let hcomm: CommGroup G:= by apply IsCyclic.commGroup
  exact CommSemigroup.to_isCommutative
}


/-- A group where every non-identity element has order 2 is abelian -/
lemma comm_of_elts_order_two {G : Type*}[Group G](h: ∀ g:G, g ≠ 1 → orderOf g = 2): IsCommutative G (fun x y ↦ x*y) where
  comm := by
    intro a b
    have h1: ∀ g:G, g*g = 1 := by{
      intro g
      by_cases hg: g = 1
      · simp[hg]
      · specialize h g hg
        rw [← pow_two]
        rw [← h, pow_orderOf_eq_one]
    }
    calc
      a * b = (a * b) * (a * b) * b⁻¹ * a⁻¹ := by group
      _ = 1 * b⁻¹ * (b*b) * a⁻¹ * (a*a) := by rw[h1 (a*b), h1 b, h1 a]; group
      _ = b * a := by group


/-- Every non-identity element of a group of order 8 has order 2, 4 or 8 -/
lemma elt_order_in_group_eight{G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8) : ∀ (g : G), g ≠ 1 → orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 8:= by
  have h3: IsPGroup 2 G:= ispgroup_of_card_8 h1 h2
  have h4: ∀ (g : G), ∃ k, orderOf g = 2 ^ k  := by apply IsPGroup.iff_orderOf.1 h3
  have h5:  ∀ (g : G), orderOf g ∣ 8 := by
    rw[← h2]
    intro g
    exact orderOf_dvd_card_univ
  have h6 : 8 = 2 ^ 3 := by simp
  have h7: ∀ (g : G), ∃ k, orderOf g = 2 ^ k ∧ k≤ 3 := by
    intro g
    specialize h4 g
    obtain ⟨ k,hk⟩ := h4
    use k
    constructor
    · exact hk
    · specialize h5 g
      rw[hk,h6] at h5
      exact Nat.pow_dvd_pow_iff_le_right'.mp h5
  intro g hg
  specialize h7 g
  obtain ⟨ k,hk1, hk2⟩ := h7
  rw[← two_add_one_eq_three] at hk2
  apply Nat.le_add_one_iff.1 at hk2
  obtain hk2|hk2 := hk2
  · rw[← one_add_one_eq_two] at hk2
    apply Nat.le_add_one_iff.1 at hk2
    obtain hk2|hk2 := hk2
    · rw[← zero_add 1] at hk2
      apply Nat.le_add_one_iff.1 at hk2
      obtain hk2|hk2 := hk2
      · rw[le_zero_iff] at hk2
        rw[hk2] at hk1
        simp at hk1
        contradiction
      · simp[hk1,hk2]
    · simp[hk1,hk2]
  · simp[hk1,hk2]


/-- A non-abelian group of order 8 has an element of order 4 -/
lemma elt_order_four_of_noncomm{G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8) : (¬ (IsCommutative G (fun x y ↦ x*y)) ) → ∃ g:G, orderOf g = 4:= by {
  have h3: ∀ (g : G), g ≠ 1 → orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 8 := by apply elt_order_in_group_eight h1 h2
  intro hnoncomm
  by_contra hcon
  push_neg at hcon
  have h9: ∀ (g : G), g≠ 1 → orderOf g = 2 := by{
    intro g hg
    specialize h3 g hg
    by_contra hc
    push_neg at hc
    specialize hcon g
    obtain h3|h3|h3 := h3
    · contradiction
    · contradiction
    · have hcomm: IsCommutative G (fun x y ↦ x*y) :=  by apply comm_of_elt_order_eight h1 h2 g h3
      contradiction
  }
  have hcomm: IsCommutative G (fun x y ↦ x*y) := by apply comm_of_elts_order_two h9
  contradiction
}


/-- Every non-abelian group of order 8 is isomorphic to `DihedralGroup 4` or `QuaternionGroup 2`.   -/
lemma noncomm_groups_order_eight{G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8)(hnoncomm: ¬ (IsCommutative G (fun x y ↦ x*y))): Nonempty (G ≃* (DihedralGroup 4)) ∨ Nonempty (G ≃* (QuaternionGroup 2))  :=  by
  obtain⟨a,ha⟩ := elt_order_four_of_noncomm h1 h2 hnoncomm
  have A: Subgroup G:= {
    carrier := Subgroup.zpowers a
    mul_mem' := by exact fun {a_1 b} a_2 a_3 ↦ mul_mem a_2 a_3
    one_mem' := by exact one_mem (Subgroup.zpowers a)
    inv_mem' := by simp
  }
  have h3: Fintype A := by exact Fintype.ofFinite (↥A)
  have h4: orderOf a = Nat.card (↥Subgroup.zpowers a) := by apply order_eq_card_zpowers' a
  rw[ha] at h4
  sorry


/-- Every group of order 8 is isomorphic to one of `ZMod 8`, `(ZMod 4) × (ZMod 2)`, `ZMod 2 × ZMod 2 × ZMod 2`, `DihedralGroup 4`, `QuaternionGroup 2`.   -/
lemma groups_order_eight {G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8): (Nonempty (G ≃* (ZMod 8)) ∨ Nonempty (G ≃*((ZMod 4) ×  (ZMod 2))) ∨ Nonempty (G ≃* (ZMod 2 × ZMod 2 × ZMod 2)) ) ∨ Nonempty (G ≃* (DihedralGroup 4)) ∨ Nonempty (G ≃* (QuaternionGroup 2))  :=  by
  by_cases hcomm: IsCommutative G (fun x y ↦ x*y)
  · left
    apply comm_groups_order_eight h1 h2 hcomm
  · right
    apply noncomm_groups_order_eight h1 h2 hcomm








/-- If a group of order 8 has an element of order 8, then it is isomorphic to  `ZMod 8` -/
lemma zmod_eight_of_elt_order_eight {G : Type*} [Group G](h1: Fintype G)(h2: Fintype.card G = 8)(g:G)(hg: orderOf g = 8): Nonempty (G≃* (ZMod 8)):= by {
  -- obtain ⟨g,hg⟩ := h3
  have h4: orderOf g = Fintype.card G:= by simp[h2,hg]
  have h5: IsCyclic G:= by apply isCyclic_of_orderOf_eq_card g h4
  have hcomm: CommGroup G:= by apply IsCyclic.commGroup
  obtain ⟨ g',h'⟩ := h5

  have f: (G ≃* (ZMod 8)) :={
    toFun := sorry
    invFun := fun (n:ZMod 8 )↦ (g') ^(n:ℤ)
    left_inv := by sorry
    right_inv := by sorry
    map_mul' := sorry
  }
  exact Nonempty.intro f
}


/-- A group of order 8 where every non-identity element has order 2 is isomorphic to `ZMod 2 × ZMod 2 × ZMod 2` -/
lemma zmod2_zmod2_zmod2_of_elts_order_two {G : Type*}[Group G](h1: Fintype G)(h2: Fintype.card G = 8)(h3: ∀ g:G, g ≠ 1 → orderOf g = 2): Nonempty (G ≃* (ZMod 2 × ZMod 2 × ZMod 2)):= by {
  have hcomm: IsCommutative G (fun x y ↦ x*y):= by apply comm_of_elts_order_two h3
  have h6:2 < Fintype.card G :=by simp[h2]
  have h7: ∃ a b :G, a≠ b ∧ a≠ 1 ∧ b≠1 := by
    obtain ⟨ a,b,c,habc⟩ := Fintype.two_lt_card_iff.1 h6
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
  obtain ⟨a,b,hab⟩ := h7
  have H: Subgroup G := {
    carrier := Subgroup.closure {a,b}
    mul_mem' := by
      intro x y hx hy
      simp
      exact Subgroup.mul_mem (Subgroup.closure {a, b}) hx hy
    one_mem' := by
      simp
      exact Subgroup.one_mem (Subgroup.closure {a, b})
    inv_mem' := by simp
  }
  sorry
}

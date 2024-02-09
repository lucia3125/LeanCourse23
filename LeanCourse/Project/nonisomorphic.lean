/- This file contains the proofs that (the multiplicative versions of) the groups `ZMod 8`,
`(ZMod 4) × (ZMod 2)`, `ZMod 2 × ZMod 2 × ZMod 2`, `DihedralGroup 4`, `QuaternionGroup 2`
are pairwise non-isomorphic. -/

import LeanCourse.Common
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion


lemma addOrderOf_elt_zmodn_dvd_n{n:ℕ}[NeZero n](a: ZMod n): addOrderOf a ∣ n:= by
  have: Fintype (ZMod n):= by refine ZMod.fintype n
  have ha: addOrderOf a ∣ Fintype.card (ZMod n) := by apply addOrderOf_dvd_card_univ
  simp at ha
  exact ha


/-- If the order of `x.1` divides `n` and the order of `x.2` divides `n`, then order of `x`  divides `n` -/
lemma addOrderOf_prod_dvd{A B: Type*}[AddMonoid A][AddMonoid B]{n:ℕ}(x : A × B) (hx1: addOrderOf x.1∣n)(hx2: addOrderOf x.2∣ n): addOrderOf x ∣ n := by
  rw[Prod.add_orderOf x]
  apply lcm_dvd_iff.2
  constructor
  · exact hx1
  · exact hx2


/-- Order of any element in `ZMod 2 × ZMod 2 × ZMod 2` divides 2 -/
lemma addOrderOf_elt_zmod2zmod2zmod2(a: ZMod 2 × ZMod 2 × ZMod 2): addOrderOf a ∣ 2 := by
  repeat
    apply addOrderOf_prod_dvd _ _ _
    apply addOrderOf_elt_zmodn_dvd_n  _
  apply addOrderOf_elt_zmodn_dvd_n  _


lemma zmod8_not_isom_zmod4zmod2: IsEmpty ( Multiplicative (ZMod 8) ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2) ) := by
  have h:  IsEmpty (Multiplicative (ZMod 8) ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2) ) ↔ IsEmpty (  (  (ZMod 8 ) ) ≃+ ZMod 4 × ZMod 2) := by
    have: (Multiplicative (ZMod 8 ) ≃* Multiplicative (ZMod 4 × ZMod 2 )) ≃ ( Additive ( Multiplicative (ZMod 8 ) ) ≃+ ZMod 4 × ZMod 2) := by exact MulEquiv.toAdditive'
    exact Equiv.isEmpty_congr this
  rw[h]
  let Z2 :=  (ZMod 2)
  let Z4 :=  (ZMod 4)
  by_contra hcon
  obtain ⟨f⟩ := not_isEmpty_iff.mp hcon
  have ha1 (a: Z4): addOrderOf a ∣ 4 := by apply addOrderOf_elt_zmodn_dvd_n a
  have ha2 (a: Z2): addOrderOf a ∣ 4 := by simp[dvd_trans (addOrderOf_elt_zmodn_dvd_n a)]
  have ha3 (a: Z4 × Z2): addOrderOf a ∣ 4:= by exact addOrderOf_prod_dvd a (ha1 a.1) (ha2 a.2)
  have ha4 (a: Z4 × Z2): 4 • a = 0 := by apply addOrderOf_dvd_iff_nsmul_eq_zero.1 (ha3 a)
  have hf3: f 4 = 0:= by
    calc
      f 4 = f (2 + 2):= by ring
      _= f 2 + f 2:= by exact AddEquiv.map_add f 2 2
      _= f (1+1) + f (1+1) := by ring
      _= (f 1 + f 1) + (f 1 + f 1) := by aesop
      _= 4 • (f 1):= by ring
      _= 0 := by exact ha4 (f 1)
  have h: f.invFun (f (4:ZMod 8)) = f.invFun 0 := by exact congrArg f.invFun hf3
  simp at h


/-- In any monoid isomorphic to `ZMod 2 × ZMod 2 × ZMod 2`, `0 = 2` holds -/
lemma zero_eq_two_of_isom_zmod2zmod2zmod2{A: Type*}[AddMonoidWithOne A](f: A ≃+ ZMod 2 × ZMod 2 × ZMod 2): (0:A) = (2:A) := by
  have h3: (2:A) = 1+1:= by exact one_add_one_eq_two.symm
  have hf1: f 2 = 0:= by aesop
  have h: f.invFun (f 0) = f.invFun (f 2) := by rw[f.map_zero,hf1]
  simp at h
  exact h


lemma zmod8_not_isom_zmod2zmod2zmod2: IsEmpty ( Multiplicative (ZMod 8) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ) := by
  have h:  IsEmpty (Multiplicative (ZMod 8) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ↔ IsEmpty (  (  (ZMod 8 ) ) ≃+ ZMod 2 × ZMod 2 × ZMod 2) := by
    have: (Multiplicative (ZMod 8 ) ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) ≃ ( Additive ( Multiplicative (ZMod 8 ) ) ≃+ ZMod 2 × ZMod 2 × ZMod 2) := by exact MulEquiv.toAdditive'
    exact Equiv.isEmpty_congr this
  rw[h]
  by_contra hcon
  obtain ⟨f⟩ := not_isEmpty_iff.mp hcon
  have: (0:ZMod 8) = 2:= by apply zero_eq_two_of_isom_zmod2zmod2zmod2 f
  contradiction


lemma zmod4zmod2_not_isom_zmod2zmod2zmod2: IsEmpty (Multiplicative (ZMod 4) × Multiplicative (ZMod 2) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have h:  IsEmpty (Multiplicative (ZMod 4) × Multiplicative (ZMod 2) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ↔ IsEmpty (  (  (ZMod 4 × ZMod 2 ) ) ≃+ ZMod 2 × ZMod 2 × ZMod 2) := by
    have: (Multiplicative (ZMod 4 × ZMod 2) ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) ≃ ( Additive ( Multiplicative (ZMod 4 × ZMod 2 ) ) ≃+ ZMod 2 × ZMod 2 × ZMod 2) := by exact MulEquiv.toAdditive'
    exact Equiv.isEmpty_congr this
  rw[h]
  by_contra hcon
  obtain ⟨f⟩ := not_isEmpty_iff.mp hcon
  have: (0 : ZMod 4 × ZMod 2) = 2:= by apply zero_eq_two_of_isom_zmod2zmod2zmod2 f
  contradiction


/-- Given two elements in a group `G` which do not commute, it follows that there is no isomorphism from `G` to a given commutative group `H` -/
lemma not_isom_comm_of_two_elts_not_comm{G H:Type*}[Group G][CommGroup H]{x y:G}(h: x * y ≠ y * x): IsEmpty (G ≃* H ) := by
  by_contra hcon
  obtain ⟨f⟩  := not_isEmpty_iff.mp hcon
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
lemma D4_not_isom_comm{A:Type*}[CommGroup A]: IsEmpty (DihedralGroup 4 ≃* A ) := by
  have h: (DihedralGroup.sr 0:DihedralGroup 4) * DihedralGroup.r 1 ≠ DihedralGroup.r 1 * DihedralGroup.sr 0 := by simp
  apply not_isom_comm_of_two_elts_not_comm h

lemma D4_not_isom_zmod8: IsEmpty (DihedralGroup 4 ≃* Multiplicative (ZMod 8) ) := by apply D4_not_isom_comm

lemma D4_not_isom_zmod4zmod2: IsEmpty (DihedralGroup 4 ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2) ) := by apply D4_not_isom_comm

lemma D4_not_isom_zmod2zmod2zmod2: IsEmpty (DihedralGroup 4 ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ) := by apply D4_not_isom_comm


/-- `QuaternionGroup 2` is not isomorphic to a given commutative group  -/
lemma Q2_not_isom_comm{A:Type*}[CommGroup A]: IsEmpty (QuaternionGroup 2 ≃* A ) := by
  have h:(QuaternionGroup.xa 0 :QuaternionGroup 2)* QuaternionGroup.a 1 ≠  QuaternionGroup.a 1 * QuaternionGroup.xa 0 := by simp
  apply not_isom_comm_of_two_elts_not_comm h

lemma Q2_not_isom_zmod8: IsEmpty (QuaternionGroup 2 ≃* Multiplicative (ZMod 8) ) := by apply Q2_not_isom_comm

lemma Q2_not_isom_zmod4zmod2: IsEmpty (QuaternionGroup 2 ≃* Multiplicative (ZMod 4 )× Multiplicative (ZMod 2) ) := by apply Q2_not_isom_comm

lemma Q2_not_isom_zmod2zmod2zmod2: IsEmpty (QuaternionGroup 2 ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ) := by apply Q2_not_isom_comm

lemma Q2_a(i:ZMod (2*2)): orderOf (QuaternionGroup.a i :QuaternionGroup 2) = 2 → QuaternionGroup.a i = QuaternionGroup.a 2:= by
  match i with
  | 0 => intro h
         have: (QuaternionGroup.a 0 : QuaternionGroup 2) =1:= by simp
         rw[this,orderOf_one] at h
         contradiction
  | 1 => simp
  | 2 => simp
  | 3 => intro h; rw[QuaternionGroup.orderOf_a] at h; simp at h

lemma Q2_a_of_orderOf_two (g:QuaternionGroup 2) :  orderOf g = 2 → g = QuaternionGroup.a 2 := by
  match g with
    | QuaternionGroup.a i => apply Q2_a i
    | QuaternionGroup.xa i => simp


open DihedralGroup

/--`DihedralGroup 4` and `QuaternionGroup 2` are not isomorphic-/
lemma D4_not_isom_Q2: IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2) := by
  by_contra hcon
  obtain ⟨f⟩ := not_isEmpty_iff.mp hcon
  have hf (x: DihedralGroup 4): orderOf (f x) = orderOf x := by apply orderOf_injective f (MulEquiv.injective f) x
  let x:=  r (2:ZMod 4)
  let y:= sr (0:ZMod 4)
  have hr: f x = f y := by
    apply Eq.trans
    · apply Q2_a_of_orderOf_two
      rw[ hf x]
      apply (orderOf_eq_iff (by simp)).2
      simp
    · symm
      apply Q2_a_of_orderOf_two
      rw[hf y]
      apply (orderOf_eq_iff (by simp)).2
      simp
  have hf1: f.invFun (f x) = f.invFun (f y):= by exact congrArg f.invFun hr
  simp at hf1

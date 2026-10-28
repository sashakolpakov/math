import OAI.RepresentationTheory.Weil.Local.FiniteQuadratic
import Mathlib.GroupTheory.Coset.Basic

/-! # Finite Quadratic Of -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

section

/-! Restriction and orthogonality for finite quadratic characters. -/

open scoped Classical ComplexConjugate

variable {A : Type*} [AddCommGroup A]

def FiniteQuadratic.Construction.QuadraticCharacter.restrict (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A) : FiniteQuadratic.Construction.QuadraticCharacter H where
  toFun x := q x.val
  polar :=
    { toFun x := (q.polar x.val).compAddMonoidHom H.subtype
      map_zero_eq_one' := by ext y; simp
      map_add_eq_mul' x y := by ext z; simp [q.polar.map_add_eq_mul] }
  map_zero := q.map_zero
  map_neg x := q.map_neg x.val
  map_add x y := q.map_add x.val y.val
  norm_eq_one x := q.norm_eq_one x.val

def FiniteQuadratic.Construction.QuadraticCharacter.orthogonal (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A) : AddSubgroup A where
  carrier := {x | ∀ y ∈ H, q.polar x y = 1}
  zero_mem' := by simp
  add_mem' {x y} hx hy z hz := by
    rw [q.polar.map_add_eq_mul, AddChar.mul_apply, hx z hz, hy z hz, one_mul]
  neg_mem' {x} hx y hy := by
    rw [q.polar.map_neg_eq_inv, AddChar.inv_apply, (q.polar x).map_neg_eq_inv, hx y hy, inv_one]

def FiniteQuadratic.Construction.QuadraticCharacter.Isotropic (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A) : Prop := ∀ x ∈ H, q x = 1

theorem FiniteQuadratic.Construction.QuadraticCharacter.isotropic_le_orthogonal (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : q.Isotropic H) : H ≤ q.orthogonal H := by
  intro x hx y hy
  have h := q.map_add x y
  rw [hH _ (H.add_mem hx hy), hH x hx, hH y hy, one_mul, one_mul] at h
  exact h.symm

theorem FiniteQuadratic.Construction.QuadraticCharacter.isotropic_translation (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : q.Isotropic H) {x y : A} (hx : x ∈ q.orthogonal H) (hy : y ∈ H) :
    q (x + y) = q x := by
  rw [q.map_add, hH y hy, hx y hy, mul_one, mul_one]

theorem FiniteQuadratic.Construction.QuadraticCharacter.sum_polar_subgroup [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A) (x : A) :
    (∑ y : H, q.polar x y.val) =
      if x ∈ q.orthogonal H then (Fintype.card H : ℂ) else 0 := by
  let χ : AddChar H ℂ := (q.polar x).compAddMonoidHom H.subtype
  by_cases hx : x ∈ q.orthogonal H
  · have heq : ∀ y : H, q.polar x y.val = 1 := fun y => hx y.val y.property
    simp [hx, heq]
  · rw [ite_eq_right hx]
    have hχ : χ ≠ 1 := by
      intro h
      apply hx
      intro y hy
      exact DFunLike.congr_fun h ⟨y, hy⟩
    exact AddChar.sum_eq_zero_of_ne_one hχ

theorem FiniteQuadratic.Construction.QuadraticCharacter.gauss_eq_sum_orthogonal [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : q.Isotropic H) : q.gauss = ∑ x : q.orthogonal H, q x.val := by
  have hcard : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  have hshift (h : H) : (∑ x, q (x + h.val)) = q.gauss :=
    Equiv.sum_comp (Equiv.addRight h.val) q
  calc
    _ = ∑ h : H, ∑ x, q (x + h.val) := by simp [hshift, nsmul_eq_mul]
    _ = ∑ x : A, q x * ∑ h : H, q.polar x h.val := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [q.map_add, hH h.val h.property, mul_one]
    _ = (Fintype.card H : ℂ) * ∑ x : A, if x ∈ q.orthogonal H then q x else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [q.sum_polar_subgroup]
      by_cases hx : x ∈ q.orthogonal H <;> simp [hx, mul_comm]
    _ = _ := by
      congr 1
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) q

end

section

/-! Descent of quadratic characters through isotropic subgroups in their radical. -/

open scoped Classical

variable {A : Type*} [AddCommGroup A]

def FiniteQuadratic.Construction.QuadraticCharacter.descendChar (H : AddSubgroup A) (χ : AddChar A ℂ) (hχ : ∀ x ∈ H, χ x = 1) :
    AddChar (A ⧸ H) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift H χ.toAddMonoidHom (fun x hx => hχ x hx))

theorem FiniteQuadratic.Construction.QuadraticCharacter.descendChar_mk (H : AddSubgroup A) (χ : AddChar A ℂ) (hχ : ∀ x ∈ H, χ x = 1) (x : A) :
    FiniteQuadratic.Construction.QuadraticCharacter.descendChar H χ hχ (QuotientAddGroup.mk x) = χ x := rfl

theorem FiniteQuadratic.Construction.QuadraticCharacter.polar_eq_of_quotient_rel (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : H ≤ q.orthogonal ⊤) {x y : A} (hxy : -x + y ∈ H) : q.polar x = q.polar y := by
  have hp : q.polar (-x + y) = 1 := by
    ext z
    exact hH hxy z (by trivial)
  have hy : y = x + (-x + y) := by abel
  rw [hy, q.polar.map_add_eq_mul, hp, mul_one]

theorem FiniteQuadratic.Construction.QuadraticCharacter.eq_of_quotient_rel (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hiso : q.Isotropic H) (hH : H ≤ q.orthogonal ⊤)
    {x y : A} (hxy : -x + y ∈ H) : q x = q y := by
  have hy : y = x + (-x + y) := by abel
  have hp : q.polar x (-x + y) = 1 := by
    rw [q.polar_symmetric]
    exact hH hxy x (by trivial)
  rw [hy, q.map_add, hiso _ hxy, hp, mul_one, mul_one]

def FiniteQuadratic.Construction.QuadraticCharacter.descend (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hiso : q.Isotropic H) (hH : H ≤ q.orthogonal ⊤) : FiniteQuadratic.Construction.QuadraticCharacter (A ⧸ H) where
  toFun := Quotient.lift q (fun _ _ h => q.eq_of_quotient_rel H hiso hH
    (QuotientAddGroup.leftRel_apply.mp h))
  polar :=
    { toFun := Quotient.lift
        (fun x => FiniteQuadratic.Construction.QuadraticCharacter.descendChar H (q.polar x) (fun y hy => by
          rw [q.polar_symmetric]
          exact hH hy x (by trivial)))
        (fun x y hxy => by
          ext z
          induction z using QuotientAddGroup.induction_on with
          | H z =>
            change q.polar x z = q.polar y z
            rw [q.polar_eq_of_quotient_rel H hH (QuotientAddGroup.leftRel_apply.mp hxy)])
      map_zero_eq_one' := by
        ext z
        induction z using QuotientAddGroup.induction_on with
        | H z =>
          change q.polar 0 z = 1
          simp
      map_add_eq_mul' x y := by
        induction x using QuotientAddGroup.induction_on with
        | H x =>
          induction y using QuotientAddGroup.induction_on with
          | H y =>
            ext z
            induction z using QuotientAddGroup.induction_on with
            | H z =>
              change q.polar (x + y) z = q.polar x z * q.polar y z
              rw [q.polar.map_add_eq_mul, AddChar.mul_apply] }
  map_zero := q.map_zero
  map_neg x := by
    induction x using QuotientAddGroup.induction_on with
    | H x => exact q.map_neg x
  map_add x y := by
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      induction y using QuotientAddGroup.induction_on with
      | H y => exact q.map_add x y
  norm_eq_one x := by
    induction x using QuotientAddGroup.induction_on with
    | H x => exact q.norm_eq_one x

theorem FiniteQuadratic.Construction.QuadraticCharacter.descend_mk (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hiso : q.Isotropic H) (hH : H ≤ q.orthogonal ⊤) (x : A) :
    q.descend H hiso hH (QuotientAddGroup.mk x) = q x := rfl

def FiniteQuadratic.Construction.QuadraticCharacter.quotientProductEquiv (H : AddSubgroup A) : A ≃ (A ⧸ H) × H where
  toFun x := (QuotientAddGroup.mk x, ⟨x - (QuotientAddGroup.mk x : A ⧸ H).out, by
    have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : A ⧸ H))
    simpa only [sub_eq_add_neg, add_comm] using h⟩)
  invFun p := p.1.out + p.2.val
  left_inv x := by dsimp; abel
  right_inv p := by
    rcases p with ⟨c, h⟩
    have hm : (QuotientAddGroup.mk (c.out + h.val) : A ⧸ H) = c := by
      rw [QuotientAddGroup.mk_add_of_mem _ h.property, QuotientAddGroup.out_eq']
    apply Prod.ext
    · exact hm
    · apply Subtype.ext
      dsimp only
      rw [hm]
      abel

theorem FiniteQuadratic.Construction.QuadraticCharacter.gauss_descend [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hiso : q.Isotropic H) (hH : H ≤ q.orthogonal ⊤) :
    q.gauss = (Fintype.card H : ℂ) * (q.descend H hiso hH).gauss := by
  let e := FiniteQuadratic.Construction.QuadraticCharacter.quotientProductEquiv H
  have hp (p : (A ⧸ H) × H) : q (e.symm p) = q.descend H hiso hH p.1 := by
    change q (p.1.out + p.2.val) = _
    rw [← q.descend_mk H hiso hH (p.1.out + p.2.val),
      QuotientAddGroup.mk_add_of_mem _ p.2.property, QuotientAddGroup.out_eq']
  calc
    _ = ∑ p : (A ⧸ H) × H, q (e.symm p) := (Equiv.sum_comp e.symm q).symm
    _ = _ := by
      simp only [hp, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, FiniteQuadratic.Construction.QuadraticCharacter.gauss]

theorem FiniteQuadratic.Construction.QuadraticCharacter.isotropic_subgroupOf_isotropic (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : q.Isotropic H) :
    (q.restrict (q.orthogonal H)).Isotropic (H.addSubgroupOf (q.orthogonal H)) := by
  intro x hx
  exact hH x.val hx

theorem FiniteQuadratic.Construction.QuadraticCharacter.isotropic_subgroupOf_radical (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A) :
    H.addSubgroupOf (q.orthogonal H) ≤ (q.restrict (q.orthogonal H)).orthogonal ⊤ := by
  intro x hx y _
  change q.polar x.val y.val = 1
  rw [q.polar_symmetric]
  exact y.property x.val hx

def FiniteQuadratic.Construction.QuadraticCharacter.isotropicReduction (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A) (hH : q.Isotropic H) :
    FiniteQuadratic.Construction.QuadraticCharacter (q.orthogonal H ⧸ H.addSubgroupOf (q.orthogonal H)) :=
  (q.restrict (q.orthogonal H)).descend (H.addSubgroupOf (q.orthogonal H))
    (q.isotropic_subgroupOf_isotropic H hH) (q.isotropic_subgroupOf_radical H)

theorem FiniteQuadratic.Construction.QuadraticCharacter.gauss_isotropicReduction [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : q.Isotropic H) :
    q.gauss = (Fintype.card (H.addSubgroupOf (q.orthogonal H)) : ℂ) *
      (q.isotropicReduction H hH).gauss := by
  rw [q.gauss_eq_sum_orthogonal H hH]
  exact (q.restrict (q.orthogonal H)).gauss_descend (H.addSubgroupOf (q.orthogonal H))
    (q.isotropic_subgroupOf_isotropic H hH) (q.isotropic_subgroupOf_radical H)

theorem FiniteQuadratic.Construction.QuadraticCharacter.phase_isotropicReduction [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : q.Isotropic H) :
    FunctionsMetaplectic.Construction.phase q.gauss = FunctionsMetaplectic.Construction.phase (q.isotropicReduction H hH).gauss := by
  rw [q.gauss_isotropicReduction H hH]
  exact Gaussian.Construction.phase_positive_mul (Fintype.card (H.addSubgroupOf (q.orthogonal H)) : ℝ)
    (Nat.cast_pos.mpr Fintype.card_pos) _

theorem FiniteQuadratic.Construction.QuadraticCharacter.quotient_card_lt [Fintype A] (H : AddSubgroup A) [Nontrivial H] :
    Fintype.card (A ⧸ H) < Fintype.card A := by
  have hcard := Fintype.card_congr (FiniteQuadratic.Construction.QuadraticCharacter.quotientProductEquiv H)
  rw [Fintype.card_prod] at hcard
  have hH := Fintype.one_lt_card (α := H)
  have hQ := Fintype.card_pos (α := A ⧸ H)
  nlinarith

theorem FiniteQuadratic.Construction.QuadraticCharacter.isotropicReduction_card_lt [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A)
    (H : AddSubgroup A) [Nontrivial H] (hH : q.Isotropic H) :
    Fintype.card (q.orthogonal H ⧸ H.addSubgroupOf (q.orthogonal H)) < Fintype.card A := by
  let i : H → H.addSubgroupOf (q.orthogonal H) :=
    fun x => ⟨⟨x.val, q.isotropic_le_orthogonal H hH x.property⟩, x.property⟩
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : H.addSubgroupOf (q.orthogonal H) => z.val.val) h
  let : Nontrivial (H.addSubgroupOf (q.orthogonal H)) := hi.nontrivial
  exact (FiniteQuadratic.Construction.QuadraticCharacter.quotient_card_lt (H.addSubgroupOf (q.orthogonal H))).trans_le
    (Fintype.card_le_of_injective _ Subtype.val_injective)

end

section

/-! Splitting off a nondegenerate subgroup of a finite quadratic character. -/

open scoped Classical

theorem FiniteQuadraticOf.Construction.phase_mul (z w : ℂ) : FunctionsMetaplectic.Construction.phase (z * w) = FunctionsMetaplectic.Construction.phase z * FunctionsMetaplectic.Construction.phase w := by
  simp only [FunctionsMetaplectic.Construction.phase, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

variable {A : Type*} [AddCommGroup A]

def FiniteQuadratic.Construction.QuadraticCharacter.polarAddHom (q : FiniteQuadratic.Construction.QuadraticCharacter A) : A →+ AddChar A ℂ where
  toFun := q.polar
  map_zero' := q.polar.map_zero_eq_one
  map_add' := q.polar.map_add_eq_mul

theorem FiniteQuadratic.Construction.QuadraticCharacter.polarAddHom_injective (q : FiniteQuadratic.Construction.QuadraticCharacter A) (hq : q.Nondegenerate) :
    Function.Injective q.polarAddHom := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hq
  change q.polarAddHom (x - y) = 0
  rw [map_sub, hxy, sub_self]

def FiniteQuadratic.Construction.QuadraticCharacter.polarEquiv [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (hq : q.Nondegenerate) :
    A ≃+ AddChar A ℂ :=
  AddEquiv.ofBijective q.polarAddHom (by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨q.polarAddHom_injective hq, (AddChar.card_eq (α := A)).symm⟩)

def FiniteQuadratic.Construction.QuadraticCharacter.restrictedPolar (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A) : A →+ AddChar H ℂ where
  toFun x := (q.polar x).compAddMonoidHom H.subtype
  map_zero' := by ext h; simp
  map_add' x y := by ext h; simp [q.polar.map_add_eq_mul]

theorem FiniteQuadratic.Construction.QuadraticCharacter.restrictedPolar_eq_zero (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A) (x : A) :
    q.restrictedPolar H x = 0 ↔ x ∈ q.orthogonal H := by
  constructor
  · intro h y hy
    exact DFunLike.congr_fun h ⟨y, hy⟩
  · intro h
    ext y
    exact h y.val y.property

def FiniteQuadratic.Construction.QuadraticCharacter.orthogonalSplit [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : (q.restrict H).Nondegenerate) : H × q.orthogonal H ≃+ A := by
  let d := (q.restrict H).polarEquiv hH
  let p : A →+ H := d.symm.toAddMonoidHom.comp (q.restrictedPolar H)
  have hd (x : A) : q.restrictedPolar H (p x).val = q.restrictedPolar H x :=
    d.apply_symm_apply _
  have hHid (x : H) : p x.val = x := d.symm_apply_apply x
  have hPid (x : q.orthogonal H) : p x.val = 0 := by
    change d.symm (q.restrictedPolar H x.val) = 0
    rw [(q.restrictedPolar_eq_zero H x.val).mpr x.property, d.symm.map_zero]
  let l : H × q.orthogonal H →+ A :=
    { toFun x := x.1.val + x.2.val
      map_zero' := by simp
      map_add' x y := by change _ + _ + (_ + _) = _; abel }
  apply AddEquiv.ofBijective l
  constructor
  · intro x y hxy
    have h1 : x.1 = y.1 := by
      have h := congrArg p hxy
      change p (x.1.val + x.2.val) = p (y.1.val + y.2.val) at h
      simpa only [_root_.map_add, hHid, hPid, add_zero] using h
    have h2 : x.2 = y.2 := by
      apply Subtype.ext
      change x.1.val + x.2.val = y.1.val + y.2.val at hxy
      rw [h1] at hxy
      exact add_left_cancel hxy
    exact Prod.ext h1 h2
  · intro x
    have hz : x - (p x).val ∈ q.orthogonal H := by
      apply (q.restrictedPolar_eq_zero H _).mp
      rw [map_sub, hd, sub_self]
    refine ⟨(p x, ⟨x - (p x).val, hz⟩), ?_⟩
    change (p x).val + (x - (p x).val) = x
    abel

theorem FiniteQuadratic.Construction.QuadraticCharacter.orthogonalSplit_apply [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : (q.restrict H).Nondegenerate) (x : H × q.orthogonal H) :
    q.orthogonalSplit H hH x = x.1.val + x.2.val := rfl

theorem FiniteQuadratic.Construction.QuadraticCharacter.gauss_orthogonalSplit [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : (q.restrict H).Nondegenerate) :
    q.gauss = (q.restrict H).gauss * (q.restrict (q.orthogonal H)).gauss := by
  have hp (x : H × q.orthogonal H) : q (q.orthogonalSplit H hH x) = q x.1.val * q x.2.val := by
    rw [q.orthogonalSplit_apply, q.map_add, q.polar_symmetric, x.2.property x.1.val x.1.property, mul_one]
  calc
    _ = ∑ x : H × q.orthogonal H, q (q.orthogonalSplit H hH x) :=
      (Equiv.sum_comp (q.orthogonalSplit H hH).toEquiv q).symm
    _ = _ := by
      simp only [hp, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, FiniteQuadratic.Construction.QuadraticCharacter.gauss, FiniteQuadratic.Construction.QuadraticCharacter.restrict]

theorem FiniteQuadratic.Construction.QuadraticCharacter.phase_orthogonalSplit [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    (hH : (q.restrict H).Nondegenerate) :
    FunctionsMetaplectic.Construction.phase q.gauss = FunctionsMetaplectic.Construction.phase (q.restrict H).gauss * FunctionsMetaplectic.Construction.phase (q.restrict (q.orthogonal H)).gauss := by
  rw [q.gauss_orthogonalSplit H hH, FiniteQuadraticOf.Construction.phase_mul]

theorem FiniteQuadratic.Construction.QuadraticCharacter.orthogonal_card_lt [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (H : AddSubgroup A)
    [Nontrivial H] (hH : (q.restrict H).Nondegenerate) :
    Fintype.card (q.orthogonal H) < Fintype.card A := by
  have hcard := Fintype.card_congr (q.orthogonalSplit H hH).toEquiv
  rw [Fintype.card_prod] at hcard
  have hHcard := Fintype.one_lt_card (α := H)
  have hPcard := Fintype.card_pos (α := q.orthogonal H)
  nlinarith

end

/-! The small two-primary Gauss sums in the finite quadratic phase calculation. -/

open scoped Classical ComplexConjugate

theorem FiniteQuadraticOf.Construction.phase_pow_of_positive_power (z : ℂ) (n : ℕ) (r : ℝ) (hr : 0 < r)
    (hz : z ^ n = (r : ℂ)) : FunctionsMetaplectic.Construction.phase z ^ n = 1 := by
  have hnorm : ‖z‖ ^ n = r := by
    have h := congrArg norm hz
    simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using h
  rw [FunctionsMetaplectic.Construction.phase, div_pow, hz, ← Complex.ofReal_pow, hnorm, div_self (Complex.ofReal_ne_zero.mpr hr.ne')]

theorem FiniteQuadraticOf.Construction.complex_fourth_roots_cases (z : ℂ) (hz : z ^ 4 = 1) :
    z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I := by
  have hsq : (z ^ 2) ^ 2 = 1 := by rwa [← pow_mul]
  rcases sq_eq_one_iff.mp hsq with h | h
  · rcases sq_eq_one_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hi : z ^ 2 = Complex.I ^ 2 := by rw [h, Complex.I_sq]
    exact Or.inr (Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp hi))

theorem FiniteQuadraticOf.Construction.phase_one_add_fourth_root_eighth (z : ℂ) (hz : z ^ 4 = 1) (hne : 1 + z ≠ 0) :
    FunctionsMetaplectic.Construction.phase (1 + z) ^ 8 = 1 := by
  rcases FiniteQuadraticOf.Construction.complex_fourth_roots_cases z hz with rfl | rfl | rfl | rfl
  · have h : FunctionsMetaplectic.Construction.phase (1 + (1 : ℂ)) = 1 := by
      convert! Gaussian.Construction.phase_positive_real 2 (by norm_num) using 1
      norm_num
    rw [h, one_pow]
  · exact (hne (by ring)).elim
  · apply FiniteQuadraticOf.Construction.phase_pow_of_positive_power _ 8 16 (by norm_num)
    ring_nf
    rw [Complex.I_pow_eq_pow_mod 5, Complex.I_pow_eq_pow_mod 6,
      Complex.I_pow_eq_pow_mod 7, Complex.I_pow_eq_pow_mod 8]
    norm_num [Complex.I_sq, Complex.I_pow_three]
    ring
  · apply FiniteQuadraticOf.Construction.phase_pow_of_positive_power _ 8 16 (by norm_num)
    ring_nf
    rw [Complex.I_pow_eq_pow_mod 5, Complex.I_pow_eq_pow_mod 6,
      Complex.I_pow_eq_pow_mod 7, Complex.I_pow_eq_pow_mod 8]
    norm_num [Complex.I_sq, Complex.I_pow_three]
    ring

theorem FiniteQuadraticOf.Construction.phase_two : FunctionsMetaplectic.Construction.phase (2 : ℂ) = 1 := by
  convert! Gaussian.Construction.phase_positive_real 2 (by norm_num) using 1

theorem FiniteQuadratic.Construction.QuadraticCharacter.gauss_zmod_two (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod 2)) : q.gauss = 1 + q 1 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  simp [FiniteQuadratic.Construction.QuadraticCharacter.gauss, hu, q.map_zero]

theorem FiniteQuadratic.Construction.QuadraticCharacter.phase_gauss_zmod_two (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod 2)) (hq : q.gauss ≠ 0) :
    FunctionsMetaplectic.Construction.phase q.gauss ^ 8 = 1 := by
  rw [q.gauss_zmod_two] at hq ⊢
  apply FiniteQuadraticOf.Construction.phase_one_add_fourth_root_eighth _ _ hq
  have h := q.map_nsmul 2 1
  rw [show 2 • (1 : ZMod 2) = 0 by decide, q.map_zero] at h
  simpa only [Nat.reducePow] using h.symm

theorem FiniteQuadratic.Construction.QuadraticCharacter.gauss_zmod_four (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod 4)) :
    q.gauss = 1 + q 1 + q 1 ^ 4 + q 1 := by
  have htwo : q 2 = q 1 ^ 4 := by
    have h := q.map_nsmul 2 1
    simpa using h
  have hthree : q 3 = q 1 := q.map_neg 1
  have hu : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [FiniteQuadratic.Construction.QuadraticCharacter.gauss, hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, q.map_zero, htwo, hthree]
  ring

theorem FiniteQuadratic.Construction.QuadraticCharacter.phase_gauss_zmod_four (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod 4)) (hq : q.gauss ≠ 0) :
    FunctionsMetaplectic.Construction.phase q.gauss ^ 8 = 1 := by
  have hz8 : q 1 ^ 8 = 1 := by
    have h := q.map_nsmul 3 1
    have hthree : q (3 • (1 : ZMod 4)) = q 1 := q.map_neg 1
    rw [hthree] at h
    apply mul_right_cancel₀ (q.ne_zero 1)
    simpa only [one_mul, ← pow_succ, Nat.reducePow] using h.symm
  have hz4 : (q 1 ^ 4) ^ 2 = 1 := by rwa [← pow_mul]
  rcases sq_eq_one_iff.mp hz4 with hz4 | hz4
  · have hg : q.gauss = (2 : ℂ) * (1 + q 1) := by rw [q.gauss_zmod_four, hz4]; ring
    have hne : 1 + q 1 ≠ 0 := by intro h; apply hq; rw [hg, h, mul_zero]
    rw [hg, FiniteQuadraticOf.Construction.phase_mul, FiniteQuadraticOf.Construction.phase_two, one_mul]
    exact FiniteQuadraticOf.Construction.phase_one_add_fourth_root_eighth _ hz4 hne
  · have hg : q.gauss = (2 : ℂ) * q 1 := by rw [q.gauss_zmod_four, hz4]; ring
    rw [hg, FiniteQuadraticOf.Construction.phase_mul, FiniteQuadraticOf.Construction.phase_two, one_mul]
    simpa only [FunctionsMetaplectic.Construction.phase, q.norm_eq_one, Complex.ofReal_one, div_one] using hz8

end

end OAI.RepresentationTheory.Weil.Local

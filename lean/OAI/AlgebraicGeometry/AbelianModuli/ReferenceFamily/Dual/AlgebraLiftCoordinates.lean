import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftDerivations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalDerivations
import Mathlib.Algebra.DualNumber

/-! # Algebra Lift Coordinates -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates.DualCoefficientLifts

/-! Actual dual-number algebra lifts over an arbitrary coefficient ring
are the linear dual of the smooth section's conormal. These constructions
retain nilpotent coefficients and require no field hypothesis. -/

variable (C : Type) [CommRing C]

def reduction : DualNumber C →+* C := (TrivSqZeroExt.fstHom C C C).toRingHom

def ideal : Ideal (DualNumber C) := RingHom.ker (reduction C)

theorem ideal_square : ideal C ^ 2 = ⊥ := by
  apply le_antisymm
  · rw [pow_two]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change x * y = 0
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    apply TrivSqZeroExt.ext
    · change x.fst * y.fst = 0
      rw [hx, zero_mul]
    · rw [DualNumber.snd_mul, hx, hy, zero_mul, mul_zero, add_zero]
      rfl
  · exact bot_le

def idealEquiv : ideal C ≃ₗ[C] C where
  toFun v := v.val.snd
  invFun c := ⟨TrivSqZeroExt.inr c, by change (TrivSqZeroExt.inr c : DualNumber C).fst = 0; rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · exact v.property.symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (R B : Type) [CommRing R] [CommRing B]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

def derivationIdealEquiv : Derivation R B (ideal C) ≃ₗ[C] Derivation R B C where
  toEquiv := ((idealEquiv C).restrictScalars B).compDer.toEquiv
  map_add' := ((idealEquiv C).restrictScalars B).compDer.map_add
  map_smul' c d := by
    apply Derivation.ext
    intro b
    exact (idealEquiv C).map_smul c (d b)

def Space := PELModuli.IntegralModel.Relative.LiftDerivations.RelativeLifts.module R B (DualNumber C) (ideal C) (ideal_square C)

instance : AddCommGroup (Space C R B) :=
  inferInstanceAs (AddCommGroup (PELModuli.IntegralModel.Relative.LiftDerivations.RelativeLifts.module R B (DualNumber C) (ideal C) (ideal_square C)))

instance : Module (DualNumber C) (Space C R B) :=
  inferInstanceAs (Module (DualNumber C)
    (PELModuli.IntegralModel.Relative.LiftDerivations.RelativeLifts.module R B (DualNumber C) (ideal C) (ideal_square C)))

instance : Module C (Space C R B) := Module.compHom (Space C R B) (algebraMap C (DualNumber C))

instance : IsScalarTower C (DualNumber C) (Space C R B) := by
  constructor
  intro a b v
  change (a • b) • v = (algebraMap C (DualNumber C) a) • (b • v)
  have h : (a • b : DualNumber C) = algebraMap C (DualNumber C) a * b := by
    apply TrivSqZeroExt.ext <;>
      simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, mul_smul]

def derivationEquiv : Space C R B ≃ₗ[C] Derivation R B C := by
  let e : Space C R B ≃ₗ[DualNumber C] Derivation R B (ideal C) :=
    PELModuli.IntegralModel.Relative.LiftDerivations.RelativeLifts.derivationEquiv R B (DualNumber C) (ideal C) (ideal_square C)
  exact (e.restrictScalars C).trans (derivationIdealEquiv C R B)

theorem derivationEquiv_apply (v : Space C R B) (b : B) :
    derivationEquiv C R B v b = (v.val.hom b).snd := by
  change (v.val.hom b - algebraMap B (DualNumber C) b).snd = (v.val.hom b).snd
  rw [TrivSqZeroExt.snd_sub, IsScalarTower.algebraMap_apply B C (DualNumber C),
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, sub_zero]

variable [Algebra B R] [IsScalarTower R B R] [IsScalarTower B R C]
  [Algebra.FormallySmooth R B]

def conormalEquiv : Space C R B ≃ₗ[C]
    ((RingHom.ker (algebraMap B R)).Cotangent →ₗ[R] C) :=
  (derivationEquiv C R B).trans (PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv R B C)

theorem conormalEquiv_toCotangent (v : Space C R B) (b : RingHom.ker (algebraMap B R)) :
    conormalEquiv C R B v (Ideal.toCotangent _ b) = (v.val.hom b).snd := by
  change PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv R B C (derivationEquiv C R B v)
    (Ideal.toCotangent _ b) = _
  rw [PELModuli.IntegralModel.Section.ConormalDerivations.SectionConormal.derivationConormalEquiv_toCotangent, derivationEquiv_apply]

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates.DualCoefficientLifts

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates

/-! Algebra maps to actual dual numbers with a prescribed reduction
are exactly the constructed square-zero lifts, over arbitrary coefficient
algebras. This retains the original map rather than just its class. -/

variable (k B C : Type) [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]

def dualAlgebraLiftEquiv :
    {f : B →ₐ[k] DualNumber C // (TrivSqZeroExt.fstHom k C C).comp f = IsScalarTower.toAlgHom k B C} ≃
      DualCoefficientLifts.Space C k B where
  toFun f := ⟨⟨f.val.toRingHom, fun b => by
    change (f.val b - algebraMap B (DualNumber C) b).fst = 0
    rw [TrivSqZeroExt.fst_sub, IsScalarTower.algebraMap_apply B C (DualNumber C),
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
    exact sub_eq_zero.mpr (AlgHom.congr_fun f.property b)⟩, f.val.commutes⟩
  invFun v := ⟨{ v.val.hom with commutes' := v.property }, by
    apply AlgHom.ext
    intro b
    have h := v.val.congruent b
    change (v.val.hom b - algebraMap B (DualNumber C) b).fst = 0 at h
    rw [TrivSqZeroExt.fst_sub, IsScalarTower.algebraMap_apply B C (DualNumber C),
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl] at h
    exact sub_eq_zero.mp h⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    rfl

theorem dualAlgebraLiftEquiv_hom
    (f : {f : B →ₐ[k] DualNumber C // (TrivSqZeroExt.fstHom k C C).comp f = IsScalarTower.toAlgHom k B C})
    (b : B) : (dualAlgebraLiftEquiv k B C f).val.hom b = f.val b := rfl

def dualAlgebraLiftDerivationEquiv :
    {f : B →ₐ[k] DualNumber C // (TrivSqZeroExt.fstHom k C C).comp f = IsScalarTower.toAlgHom k B C} ≃
      Derivation k B C :=
  (dualAlgebraLiftEquiv k B C).trans (DualCoefficientLifts.derivationEquiv C k B).toEquiv

theorem dualAlgebraLiftDerivationEquiv_apply
    (f : {f : B →ₐ[k] DualNumber C // (TrivSqZeroExt.fstHom k C C).comp f = IsScalarTower.toAlgHom k B C})
    (b : B) : dualAlgebraLiftDerivationEquiv k B C f b = (f.val b).snd :=
  DualCoefficientLifts.derivationEquiv_apply C k B (dualAlgebraLiftEquiv k B C f) b

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates

end

end OAI

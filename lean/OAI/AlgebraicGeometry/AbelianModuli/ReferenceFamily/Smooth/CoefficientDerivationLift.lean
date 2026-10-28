import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality
import Mathlib.RingTheory.Smooth.Basic

/-! # Coefficient Derivation Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.CoefficientDerivationLift

noncomputable section

/-! Formal smoothness lifts the actual coefficient-valued dual-number
maps. Consequently, restriction of coefficient-valued derivations from a
smooth affine family to its base is surjective. -/

variable (k R S C : Type) [CommRing k] [CommRing R] [CommRing S] [CommRing C]
    [Algebra k R] [Algebra k S] [Algebra k C] [Algebra R S] [Algebra R C] [Algebra S C]
    [IsScalarTower k R S] [IsScalarTower k R C] [IsScalarTower k S C] [IsScalarTower R S C]
    [Algebra.FormallySmooth R S]

theorem exists_smooth_dualCoefficient_lift (q : R →ₐ[k] DualNumber C)
    (hq : (TrivSqZeroExt.fstHom k C C).comp q = IsScalarTower.toAlgHom k R C) :
    ∃ f : S →ₐ[k] DualNumber C,
      (TrivSqZeroExt.fstHom k C C).comp f = IsScalarTower.toAlgHom k S C ∧
        f.comp (IsScalarTower.toAlgHom k R S) = q := by
  let twist : Algebra R (DualNumber C) := q.toRingHom.toAlgebra
  let : Module R (DualNumber C) := twist.toModule
  let : SMul R (DualNumber C) := twist.toSMul
  let : IsScalarTower k R (DualNumber C) :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := R) (A := DualNumber C) (by
      apply RingHom.ext
      intro a
      exact (q.commutes a).symm)
  let red : DualNumber C →ₐ[R] C :=
    { (TrivSqZeroExt.fstHom k C C).toRingHom with
      commutes' := fun r => AlgHom.congr_fun hq r }
  have hr : Function.Surjective red := fun c => ⟨TrivSqZeroExt.inl c, rfl⟩
  have hn : IsNilpotent (RingHom.ker red.toRingHom) :=
    ⟨2, Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C⟩
  let u := Algebra.FormallySmooth.liftOfSurjective (IsScalarTower.toAlgHom R S C) red hr hn
  refine ⟨u.restrictScalars k, ?_, ?_⟩
  · apply AlgHom.ext
    intro s
    exact Algebra.FormallySmooth.liftOfSurjective_apply (IsScalarTower.toAlgHom R S C) red hr hn s
  · apply AlgHom.ext
    intro r
    exact u.commutes r

theorem smooth_coefficientDerivationPrecomposition_surjective :
    Function.Surjective (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C) := by
  intro d
  let q := (Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C).symm d
  obtain ⟨f, hf, hfr⟩ := exists_smooth_dualCoefficient_lift k R S C q.val q.property
  refine ⟨Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k S C ⟨f, hf⟩, ?_⟩
  apply Derivation.ext
  intro r
  change Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k S C ⟨f, hf⟩ (algebraMap R S r) = d r
  rw [Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply]
  have hd : Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C q = d :=
    (Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R C).apply_symm_apply d
  rw [← hd, Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply]
  exact congrArg TrivSqZeroExt.snd (AlgHom.congr_fun hfr r)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.CoefficientDerivationLift

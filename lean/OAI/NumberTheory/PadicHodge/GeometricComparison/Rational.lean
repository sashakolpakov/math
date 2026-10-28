import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRational
import OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusCohomology

/-! # Rational -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.GeometricRationalComparison

noncomputable section

/-! Compare the original Completion Frobenius with scalar extension of the original IntegralComparison rational Frobenius on the actual geometric fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

variable {k : Type} [Field k] (A : Over (Spec (.of k))) [IsProper A.hom]

instance geometricFiber_compact : CompactSpace (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A) := by
  change CompactSpace (pullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) : Scheme)
  infer_instance

instance geometricFiber_quasiSeparated : QuasiSeparatedSpace (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A) := by
  have : IsSeparated A.hom := inferInstance
  have : QuasiSeparated A.hom := inferInstance
  let b : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiSeparated.{0}) b :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback⟩
  let f : pullback A.hom b ⟶ Spec (.of (AlgebraicClosure k)) := pullback.snd A.hom b
  have hf : QuasiSeparated f :=
    MorphismProperty.pullback_snd (P := @QuasiSeparated.{0}) A.hom b inferInstance
  exact @quasiSeparatedSpace_of_quasiSeparated _ _ f inferInstance hf

theorem geometricFrobenius_compare (p : ℕ) [Fact p.Prime]
    (A : Over (Spec (.of (ZMod p)))) [IsProper A.hom] (ℓ : ℕ) [Fact ℓ.Prime] :
    (AlgebraicRational.RationalProEtaleCoefficients.algebraicH1Equiv ℓ (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A)).toLinearMap.comp
        (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.geometricH1Frobenius ℓ (ZMod p) A) =
      ((IntegralComparison.Etale.Frobenius.geometricFrobeniusLinear ℓ p 1 (ZMod p) (by simp) A.hom 1).toLinearMap.baseChange
        (AlgebraicClosure ℚ_[ℓ])).comp (AlgebraicRational.RationalProEtaleCoefficients.algebraicH1Equiv ℓ (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.geometricFiber A)).toLinearMap := by
  rw [FrobeniusCohomology.FiniteFieldFrobeniusGeometry.geometricH1Frobenius_eq_field_pullback]
  exact AlgebraicRational.RationalProEtaleCoefficients.algebraicH1Equiv_pullback ℓ
    (IntegralComparison.Frobenius.Geometry.geometricFiberIso A.hom
      (IntegralComparison.Frobenius.Geometry.geometricFrobenius p 1 (ZMod p) (by simp)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.GeometricRationalComparison

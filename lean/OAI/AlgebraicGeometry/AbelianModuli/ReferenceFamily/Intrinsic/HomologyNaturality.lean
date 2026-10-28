import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Naturality

/-! # Homology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

noncomputable section

/-! The constructed rational period-to-homology equivalence commutes
with actual algebraic group maps. Universal coefficient evaluation
derives this from the proved naturality of normalized singular periods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem nativeHomologyPeriods_naturality {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B (IntegralMaps.IntrinsicLinearMaps.rationalLift f v) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 1
        (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) := by
  apply (Module.evalEquiv ℚ (HomologyPeriods.IntrinsicRationalPeriods.rationalHomologyOne B)).injective
  apply LinearMap.ext
  intro φ
  obtain ⟨c, rfl⟩ := (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (Betti.Scheme.schemePointSpace B.toOver) 1).surjective φ
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace B.toOver) 1 c
      (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B (IntegralMaps.IntrinsicLinearMaps.rationalLift f v)) =
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace B.toOver) 1 c
      (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 1
        (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v))
  have h := LinearMap.congr_fun (Naturality.IntrinsicRationalPeriods.nativeH1Periods_naturality f c) v
  have ha := HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A v
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 1 c)
  have hn := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 1 c (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v)
  exact (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing B (IntegralMaps.IntrinsicLinearMaps.rationalLift f v) c).trans
    (h.symm.trans (ha.symm.trans hn))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

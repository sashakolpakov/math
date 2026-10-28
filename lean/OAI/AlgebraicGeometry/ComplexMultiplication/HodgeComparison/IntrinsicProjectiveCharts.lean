import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveScheme
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolynomialCharts

/-! # Intrinsic Projective Charts -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction

noncomputable section

/-! The ordinary projective coordinates are actual holomorphic native scheme charts. -/

open scoped ContDiff _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

local instance projectiveIntegral (n : ℕ) : IsIntegral (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left :=
  ProjectiveScheme.CM.Construction.projectiveScheme_integral n
local instance projectiveSmooth (n : ℕ) : Smooth (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom :=
  Albanese.Construction.ProjectiveCover.projectiveSpace_smooth n
local instance projectiveNativeChartedSpace (n : ℕ) :
    ChartedSpace (ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) :=
  (ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticSpace_chartedSpace

def nativeProjectiveCoordinateChart (n : ℕ) (i : Fin (n + 1)) :
    OpenPartialHomeomorph (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)
      (Fin (Fintype.card {j : Fin (n + 1) // j ≠ i}) → ℂ) :=
  ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i) (PolynomialCharts.CM.Construction.polynomialRegularChart {j : Fin (n + 1) // j ≠ i})

theorem nativeProjectiveCoordinateChart_smooth (n : ℕ) (i : Fin (n + 1)) :
    ContMDiffOn 𝓘(ℂ, (ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel)
      𝓘(ℂ, Fin (Fintype.card {j : Fin (n + 1) // j ≠ i}) → ℂ) ω
      (nativeProjectiveCoordinateChart n i) (nativeProjectiveCoordinateChart n i).source := by
  have : IsIntegral (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left := ProjectiveScheme.CM.Construction.projectiveScheme_integral n
  have : Smooth (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom := Albanese.Construction.ProjectiveCover.projectiveSpace_smooth n
  exact PolynomialCharts.CM.Construction.native_affineChart_smooth (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i) _ (PolynomialCharts.CM.Construction.polynomialRegularChart_mem_atlas _)

theorem projectivePoint_eq_affinePoint_on_patch (n : ℕ) (i : Fin (n + 1))
    (q : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) (hq : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q)) :
    q = ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i
      (fun j : {j : Fin (n + 1) // j ≠ i} => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q)) := by
  have h := ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_on_patch n i
    ⟨(ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q, hq⟩
  have hq' : ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q) = q :=
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).apply_symm_apply q
  exact hq'.symm.trans h

theorem nativeProjectiveCoordinateChart_mem_source (n : ℕ) (i : Fin (n + 1))
    (q : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) (hq : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q)) :
    q ∈ (nativeProjectiveCoordinateChart n i).source := by
  rw [projectivePoint_eq_affinePoint_on_patch n i q hq]
  change ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i _ ∈
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
      (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i) '' (PolynomialCharts.CM.Construction.polynomialRegularChart {j : Fin (n + 1) // j ≠ i}).source
  refine ⟨(ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm _, ?_, rfl⟩
  trivial

theorem nativeProjectiveCoordinateChart_apply (n : ℕ) (i : Fin (n + 1))
    (q : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) (hq : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q))
    (k : Fin (Fintype.card {j : Fin (n + 1) // j ≠ i})) :
    nativeProjectiveCoordinateChart n i q k =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i ((Fintype.equivFin {j : Fin (n + 1) // j ≠ i}).symm k).val
        ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q) := by
  conv_lhs => rw [projectivePoint_eq_affinePoint_on_patch n i q hq]
  rw [nativeProjectiveCoordinateChart, ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint, ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply,
    PolynomialCharts.CM.Construction.polynomialRegularChart_apply]
  simp only [ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph_symm_apply, MvPolynomial.eval_X]

theorem projectiveCoordinates_holomorphic (n : ℕ) (i : Fin (n + 1)) :
    ContMDiffOn 𝓘(ℂ, (ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel) 𝓘(ℂ, Fin (n + 1) → ℂ) ∞
      (fun q : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q))
      {q | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q)} := by
  apply contMDiffOn_pi_space.mpr
  intro j
  by_cases hji : j = i
  · subst j
    apply contMDiffOn_const.congr
    intro q hq
    exact Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates_self i _ hq
  · let k := Fintype.equivFin {j : Fin (n + 1) // j ≠ i} ⟨j, hji⟩
    have hs := ((nativeProjectiveCoordinateChart_smooth n i).of_le
      (show (∞ : ℕ∞ω) ≤ ω from le_top)).mono (fun q hq => nativeProjectiveCoordinateChart_mem_source n i q hq)
    apply (contMDiffOn_pi_space.mp hs k).congr
    intro q hq
    have hk := nativeProjectiveCoordinateChart_apply n i q hq k
    simpa only [k, Equiv.symm_apply_apply, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates] using hk.symm

theorem nativeProjectiveCoordinateChart_mdifferentiable (n : ℕ) (i : Fin (n + 1)) :
    (nativeProjectiveCoordinateChart n i).MDifferentiable
      𝓘(ℂ, (ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel)
      𝓘(ℂ, Fin (Fintype.card {j : Fin (n + 1) // j ≠ i}) → ℂ) :=
  PolynomialCharts.CM.Construction.native_affineChart_mdifferentiable (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i) _ (PolynomialCharts.CM.Construction.polynomialRegularChart_mem_atlas _)

theorem projectiveEmbeddingCoordinates_holomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (i : Fin (V.ambientDimension + 1)) :
    ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin (V.ambientDimension + 1) → ℂ) ∞
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V) i)
      (ProjectiveGluing.CM.Construction.projectiveLiftDomain (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V)
        (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates_continuous V) i : Set V.analyticSpace) := by
  exact (projectiveCoordinates_holomorphic V.ambientDimension i).comp
    (ProjectiveScheme.CM.Construction.projectiveEmbeddingMap_holomorphic V).contMDiffOn (fun _ hx => hx)

/-- A smooth closed form of type (1,1) on the genuine analytic variety,
constructed from its actual algebraic projective embedding. -/
def varietyFubiniStudyForm (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2 :=
  ProjectiveGluing.CM.Construction.projectiveCurvatureForm (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates V) (ProjectiveScheme.CM.Construction.projectiveEmbeddingCoordinates_continuous V)
    (projectiveEmbeddingCoordinates_holomorphic V)

theorem varietyFubiniStudyForm_closed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (varietyFubiniStudyForm V) = 0 :=
  ProjectiveGluing.CM.Construction.projectiveCurvatureForm_closed _ _ _

theorem varietyFubiniStudyForm_hasBidegree (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1
      (varietyFubiniStudyForm V : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace 2) :=
  ProjectiveGluing.CM.Construction.projectiveCurvatureForm_hasBidegree _ _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction

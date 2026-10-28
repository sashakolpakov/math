import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation
import OAI.ArithmeticGeometry.Descent.CMVariety.PresentedChartPeriods

/-! # Presented Derivative Coordinates -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.PresentedDerivativeCoordinates

noncomputable section

/-!
The derivative coordinates constructed from the relative algebraic
endomorphism remain exactly the derivative coordinates after transporting
the fiber to its actual abelian-variety presentation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

namespace Abelian.ComplexAbelianPresentation

local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

variable {g : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral A.scheme.left]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]

local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom) → ℂ)

theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.derivative_in_presented_chart_coordinates
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A)
    (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) V)
    (T : V ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety)
    (hT : ∀ v, T v = mfderiv (𝓘(ℝ, ModelA)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) 1 (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ModelA) c v))
    (k : A.scheme ⟶ A.scheme) [IsMonHom k]
    (D : V →L[ℝ] V)
    (hD : ∀ v, ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ModelA) c (D v) =
      mfderiv (𝓘(ℝ, ModelA)) (𝓘(ℝ, ModelA)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k) 1
        (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ModelA) c v)) (v : V) :
    T.symm (mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.comparison.inv ≫ k ≫ P.comparison.hom)) 1 (T v)) = D v := by
  let : IsMonHom P.comparison.hom := P.comparison_group
  let J := IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent P.comparison
  let L := ChartEndomorphismDerivative.Abelian.chartTangentMap (E := ModelA) c
  let K : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety :=
    mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.comparison.inv ≫ k ≫ P.comparison.hom)) 1
  have hTJ (w : V) : T w = J (L w) := (hT w).trans
    (congrArg (fun e : ModelA →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety => e (L w))
      (IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent_real P.comparison))
  have hK : K (T v) = T (D v) :=
    (congrArg K (hTJ v)).trans
      ((IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoTangent_conjugate P.comparison k (L v)).trans
        ((congrArg J (hD v).symm).trans (hTJ (D v)).symm))
  exact (congrArg T.symm hK).trans (T.symm_apply_apply (D v))

end Abelian.ComplexAbelianPresentation

namespace Abelian

local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

variable {S V : Type} [TopologicalSpace S]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {g : ℕ} (A : S → AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [∀ s, IsIntegral (A s).scheme.left]

theorem continuousAt_presented_derivative_on_vectors
    (P : ∀ s, StandardModuli.Abelian.ComplexAbelianPresentation (A s))
    (c : ∀ s, OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A s).scheme) V)
    (T : ∀ s, V ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)
    (hT : ∀ s v, T s v =
      mfderiv (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (A s).scheme.hom) → ℂ))
        (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P s).comparison.hom) 1
        (ChartEndomorphismDerivative.Abelian.chartTangentMap
          (E := Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (A s).scheme.hom) → ℂ) (c s) v))
    (k : ∀ s, (A s).scheme ⟶ (A s).scheme) (hk : ∀ s, IsMonHom (k s))
    (D : S → V →L[ℝ] V) (v : S → V) (s₀ : S)
    (hD : ContinuousAt D s₀) (hv : ContinuousAt v s₀)
    (hcoord : ∀ᶠ s in 𝓝 s₀, ∀ w,
      ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (A s).scheme.hom) → ℂ)
        (c s) (D s w) =
      mfderiv (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (A s).scheme.hom) → ℂ))
        (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (A s).scheme.hom) → ℂ))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k s)) 1
        (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (A s).scheme.hom) → ℂ)
          (c s) w)) (d : ℕ) (e : V ≃L[ℂ] (Fin d → ℂ)) :
    ContinuousAt (fun s => e ((T s).symm
      (mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P s).variety))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((P s).comparison.inv ≫ k s ≫ (P s).comparison.hom)) 1
        (T s (v s))))) s₀ := by
  have h : ContinuousAt (fun s => e (D s (v s))) s₀ :=
    e.continuous.continuousAt.comp (hD.clm_apply hv)
  apply h.congr_of_eventuallyEq
  filter_upwards [hcoord] with s hs
  let : IsMonHom (k s) := hk s
  exact congrArg e (StandardModuli.Abelian.ComplexAbelianPresentation.derivative_in_presented_chart_coordinates
    (P s) (c s) (T s) (hT s) (k s) (D s) hs (v s))

end Abelian

end

end OAI.ArithmeticGeometry.Descent.CMVariety.PresentedDerivativeCoordinates

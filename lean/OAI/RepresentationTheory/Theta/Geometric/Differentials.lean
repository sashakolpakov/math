import OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality

/-! # Differentials -/

namespace OAI.RepresentationTheory.Theta.Geometric.Differentials

noncomputable section

/-! The canonical theta one-form has a concrete Kähler expression on a
period test algebra: sum of its two coordinate coefficients times the
coordinate differentials. Differentiation recovers the original theta
covector exactly; no identification assumption is used. -/

def coordinateAt (x : LinearTheta.BallCoordinates) (i : Fin 2) : DifferentialNaturality.functionsAt x :=
  ⟨fun y => y i, (ContinuousLinearMap.proj i : LinearTheta.BallCoordinates →L[ℂ] ℂ).differentiableAt⟩

def formCoefficientAt (ω : LinearTheta.BallCoordinates → LinearTheta.Cotangent) (x : LinearTheta.BallCoordinates)
    (hω : DifferentiableAt ℂ ω x) (i : Fin 2) : DifferentialNaturality.functionsAt x :=
  ⟨fun y => ω y (Pi.single i 1), hω.clm_apply (differentiableAt_const _)⟩

def localKaehlerForm (ω : LinearTheta.BallCoordinates → LinearTheta.Cotangent) (x : LinearTheta.BallCoordinates)
    (hω : DifferentiableAt ℂ ω x) : KaehlerDifferential ℂ (DifferentialNaturality.functionsAt x) :=
  ∑ i : Fin 2, formCoefficientAt ω x hω i •
    KaehlerDifferential.D ℂ (DifferentialNaturality.functionsAt x) (coordinateAt x i)

theorem covector_coordinates (ω : LinearTheta.Cotangent) (v : LinearTheta.BallCoordinates) :
    (∑ i : Fin 2, ω (Pi.single i 1) * v i) = ω v := by
  have hv : (∑ i : Fin 2, v i • Pi.single i (1 : ℂ)) = v := by
    ext j
    fin_cases j <;> simp
  have h := congrArg ω hv
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h

/-- The Kähler realization is exactly the original holomorphic covector. -/
theorem periodDifferential_localKaehlerForm
    (ω : LinearTheta.BallCoordinates → LinearTheta.Cotangent) (x : LinearTheta.BallCoordinates)
    (hω : DifferentiableAt ℂ ω x) :
    DifferentialNaturality.periodDifferential x (localKaehlerForm ω x hω) = ω x := by
  have hcoord (i : Fin 2) : fderiv ℂ (coordinateAt x i).val x =
      (ContinuousLinearMap.proj i : LinearTheta.BallCoordinates →L[ℂ] ℂ) :=
    (ContinuousLinearMap.proj i : LinearTheta.BallCoordinates →L[ℂ] ℂ).hasFDerivAt.fderiv
  simp only [localKaehlerForm, map_sum, DifferentialNaturality.periodDifferential_smul,
    DifferentialNaturality.periodDifferential_D, hcoord]
  ext v
  exact covector_coordinates (ω x) v

variable {ι : Type*} [Fintype ι]

def canonicalThetaKaehler
    (D : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (period : LinearTheta.BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (hperiod : DifferentiableOn ℂ (fun y => (period y).matrix) D)
    (project : LinearTheta.BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] LinearTheta.Cotangent)
    (hproject : DifferentiableOn ℂ project D)
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : D) :
    KaehlerDifferential ℂ (DifferentialNaturality.functionsAt x.val) :=
  localKaehlerForm (LinearTheta.thetaOneFormLinear period project φ) x.val
    ((LinearTheta.canonical_oneForm_holomorphic D period hperiod project hproject φ x.val x.property).differentiableAt
      (D.isOpen.mem_nhds x.property))

/-- The AdelicTheta tensor, ThetaOneForms projected form, and the Kähler period expression
all evaluate to the same actual order-one theta derivative. -/
theorem canonicalThetaKaehler_identification
    (D : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (period : LinearTheta.BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (hperiod : DifferentiableOn ℂ (fun y => (period y).matrix) D)
    (project : LinearTheta.BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] LinearTheta.Cotangent)
    (hproject : DifferentiableOn ℂ project D)
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : D) :
    DifferentialNaturality.periodDifferential x.val (canonicalThetaKaehler D period hperiod project hproject φ x) =
      project x.val (LinearTheta.canonicalFirst φ (period x.val)) :=
  periodDifferential_localKaehlerForm _ _ _

end

end OAI.RepresentationTheory.Theta.Geometric.Differentials

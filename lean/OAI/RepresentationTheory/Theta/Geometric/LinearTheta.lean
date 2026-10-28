import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
import OAI.RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice
import OAI.RepresentationTheory.Theta.Geometric.No

/-! # Linear Theta -/

namespace OAI.RepresentationTheory.Theta.Geometric.LinearTheta

noncomputable section

/-!
# GeometricTheta's canonical linear theta map

Inputs are PoissonAutomorphy's actual finite Schwartz submodule. The conversion to DerivativeFactorization
keeps the underlying function unchanged. The scalar theta sum is identified
term by term, its first derivative is DerivativeFactorization's proved first coefficient, and
projection gives exactly ThetaOneForms's formula. No input-to-form identification is
assumed. The only geometric data here are the period and the cotangent
projection already present in ThetaOneForms.
-/

open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open scoped _root_.Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι]

/-- Identity on functions, from PoissonAutomorphy's span presentation to DerivativeFactorization's subtype. -/
def toDerivativeFactorizationInput (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) : DerivativeFactorizationDefinitions.Input ι :=
  ⟨φ.val, (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff φ.val).mp φ.property⟩

@[simp] theorem toDerivativeFactorizationInput_val (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    (toDerivativeFactorizationInput φ).val = φ.val := rfl

/-- PoissonAutomorphy and DerivativeFactorization sum exactly the same rational-position terms. -/
theorem theta_eq_DerivativeFactorization (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    PoissonAutomorphyNormalizationData.theta φ Z z = DerivativeFactorizationDefinitions.theta (toDerivativeFactorizationInput φ) Z.matrix z := by
  simp only [PoissonAutomorphyNormalizationData.theta, PoissonAutomorphyNormalizationData.thetaTerm, DerivativeFactorizationDefinitions.theta, DerivativeFactorizationDefinitions.kernel,
    toDerivativeFactorizationInput_val, DerivativeFactorizationDefinitions.realPosition,
    AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply, Complex.ofReal_ratCast]
  rfl

theorem theta_terms_summable (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    Summable (fun x : ι → ℚ => PoissonAutomorphyNormalizationData.thetaTerm φ Z z x) := by
  have h := (DerivativeFactorizationAdelicLattice.theta_norm_summable (toDerivativeFactorizationInput φ) Z z).of_norm
  have heq : (fun x : ι → ℚ => PoissonAutomorphyNormalizationData.thetaTerm φ Z z x) =
      (fun x : ι → ℚ => (toDerivativeFactorizationInput φ).val (DerivativeFactorizationDefinitions.diagonal x) *
        DerivativeFactorizationDefinitions.kernel Z.matrix x z) := by
    funext x
    simp only [PoissonAutomorphyNormalizationData.thetaTerm, DerivativeFactorizationDefinitions.kernel, toDerivativeFactorizationInput_val,
      DerivativeFactorizationDefinitions.realPosition, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply, Complex.ofReal_ratCast]
    rfl
  rw [heq]
  exact h

theorem theta_add_input (φ ψ : PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    PoissonAutomorphyNormalizationData.theta (φ + ψ) Z z =
      PoissonAutomorphyNormalizationData.theta φ Z z + PoissonAutomorphyNormalizationData.theta ψ Z z := by
  simp only [PoissonAutomorphyNormalizationData.theta, PoissonAutomorphyNormalizationData.thetaTerm, Submodule.coe_add, Pi.add_apply,
    add_mul]
  exact (theta_terms_summable φ Z z).tsum_add (theta_terms_summable ψ Z z)

theorem theta_smul_input (c : ℂ) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    PoissonAutomorphyNormalizationData.theta (c • φ) Z z = c • PoissonAutomorphyNormalizationData.theta φ Z z := by
  simp only [PoissonAutomorphyNormalizationData.theta, PoissonAutomorphyNormalizationData.thetaTerm, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]

/-- The theta series as a linear map of the genuine finite Schwartz input. -/
def scalarThetaLinear (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] ((ι → ℂ) → ℂ) where
  toFun φ := PoissonAutomorphyNormalizationData.theta φ Z
  map_add' φ ψ := funext (theta_add_input φ ψ Z)
  map_smul' c φ := funext (theta_smul_input c φ Z)

def canonicalFirst (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    (ι → ℂ) →L[ℂ] ℂ := DerivativeFactorizationDefinitions.firstCoefficient (toDerivativeFactorizationInput φ) Z.matrix

theorem canonicalFirst_hasFDerivAt (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    HasFDerivAt (PoissonAutomorphyNormalizationData.theta φ Z) (canonicalFirst φ Z) 0 := by
  simpa only [canonicalFirst, funext (theta_eq_DerivativeFactorization φ Z)] using
    DerivativeFactorizationAdelicLattice.theta_hasFDerivAt_zero (toDerivativeFactorizationInput φ) Z

def canonicalCompleted (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z * PoissonAutomorphyNormalizationData.theta φ Z z

theorem canonicalCompleted_hasFDerivAt
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    HasFDerivAt (canonicalCompleted φ Z) (canonicalFirst φ Z) 0 := by
  exact AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletion_mul_hasFDerivAt_zero Z.completionForm
    (canonicalFirst_hasFDerivAt φ Z)

theorem canonicalFirst_add (φ ψ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    canonicalFirst (φ + ψ) Z = canonicalFirst φ Z + canonicalFirst ψ Z := by
  apply (canonicalFirst_hasFDerivAt (φ + ψ) Z).unique
  rw [funext (theta_add_input φ ψ Z)]
  exact (canonicalFirst_hasFDerivAt φ Z).add (canonicalFirst_hasFDerivAt ψ Z)

theorem canonicalFirst_smul (c : ℂ) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    canonicalFirst (c • φ) Z = c • canonicalFirst φ Z := by
  apply (canonicalFirst_hasFDerivAt (c • φ) Z).unique
  rw [funext (theta_smul_input c φ Z)]
  exact (canonicalFirst_hasFDerivAt φ Z).const_smul c

/-- PoissonAutomorphy's actual rational theta equation gives covariance of the canonical
first coefficient. The named hypothesis is exactly PoissonAutomorphy's final conjunct;
the finite transform and determinant branch remain its constructed ones. -/
theorem canonical_first_covariance
    [DecidableEq ι] {MpR MpF MpA : Type*}
    [Group MpR] [Group MpF] [Group MpA]
    (W : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ)
    (h_PoissonAutomorphy : ∀ (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      PoissonAutomorphyNormalizationData.theta (W.finiteAction γ φ)
          ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) =
        PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z *
          (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) Z z * PoissonAutomorphyNormalizationData.theta φ Z z))
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    (canonicalFirst (W.finiteAction γ φ) ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)).comp
        ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z) =
      PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z • canonicalFirst φ Z := by
  apply AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.theta_first_derivative_covariance ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z)
    ((PoissonAutomorphyNormalizationData.realBlocks γ).thetaCorrectionForm Z) (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z)
    (canonicalFirst_hasFDerivAt φ Z)
    (canonicalFirst_hasFDerivAt (W.finiteAction γ φ) ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z))
  intro z
  exact h_PoissonAutomorphy φ Z z

def firstThetaLinear (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] ((ι → ℂ) →L[ℂ] ℂ) where
  toFun φ := canonicalFirst φ Z
  map_add' φ ψ := canonicalFirst_add φ ψ Z
  map_smul' c φ := canonicalFirst_smul c φ Z

abbrev BallCoordinates := Fin 2 → ℂ
abbrev Cotangent := BallCoordinates →L[ℂ] ℂ

/-- The canonical order-one theta tensor before ThetaOneForms's cotangent projection.
This is the concrete linear theta map used to instantiate AdelicTheta. -/
def thetaTensorLinear (period : BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] (BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ)) where
  toFun φ x := firstThetaLinear (period x) φ
  map_add' φ ψ := by funext x; exact (firstThetaLinear (period x)).map_add φ ψ
  map_smul' c φ := by funext x; exact (firstThetaLinear (period x)).map_smul c φ

def projectTensorLinear
    (project : BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] Cotangent) :
    (BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ)) →ₗ[ℂ] (BallCoordinates → Cotangent) where
  toFun F x := project x (F x)
  map_add' F H := by funext x; exact (project x).map_add (F x) (H x)
  map_smul' c F := by funext x; exact (project x).map_smul c (F x)

/-- The canonical ThetaOneForms map, obtained by the order-one projection. -/
def thetaOneFormLinear
    (period : BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (project : BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] Cotangent) :
    PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] (BallCoordinates → Cotangent) where
  toFun φ x := project x (firstThetaLinear (period x) φ)
  map_add' φ ψ := by ext x; simp only [map_add, Pi.add_apply]
  map_smul' c φ := by ext x; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The AdelicTheta tensor map and ThetaOneForms one-form map are related by the actual
cotangent projection, definitionally on every input and period point. -/
theorem thetaOneFormLinear_eq_projectTensor
    (period : BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (project : BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] Cotangent) :
    thetaOneFormLinear period project =
      (projectTensorLinear project).comp (thetaTensorLinear period) := by
  rfl

@[simp] theorem thetaOneFormLinear_apply
    (period : BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (project : BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] Cotangent)
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : BallCoordinates) :
    thetaOneFormLinear period project φ x =
      project x (DerivativeFactorizationDefinitions.firstCoefficient (toDerivativeFactorizationInput φ) (period x).matrix) := rfl

/-- Derivative uniqueness identifies ThetaOneForms's first-coefficient interface
with the canonical one when its theta function is the actual series. -/
theorem first_identification
    (D : Set BallCoordinates)
    (period : BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (first : PoissonAutomorphyNormalizationData.finiteSchwartz ι → BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ))
    (h_ThetaOneForms_first : ∀ φ x, x ∈ D →
      HasFDerivAt (canonicalCompleted φ (period x)) (first φ x) 0)
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : BallCoordinates) (hx : x ∈ D) :
    first φ x = canonicalFirst φ (period x) :=
  (h_ThetaOneForms_first φ x hx).unique (canonicalCompleted_hasFDerivAt φ (period x))

theorem projected_identification
    (D : Set BallCoordinates)
    (period : BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (project : BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] Cotangent)
    (first : PoissonAutomorphyNormalizationData.finiteSchwartz ι → BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ))
    (h_ThetaOneForms_first : ∀ φ x, x ∈ D →
      HasFDerivAt (canonicalCompleted φ (period x)) (first φ x) 0)
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : BallCoordinates) (hx : x ∈ D) :
    project x (first φ x) = thetaOneFormLinear period project φ x := by
  rw [first_identification D period first h_ThetaOneForms_first φ x hx]
  rfl

theorem canonical_oneForm_holomorphic
    (D : Set BallCoordinates)
    (period : BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (hperiod : DifferentiableOn ℂ (fun x => (period x).matrix) D)
    (project : BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] Cotangent)
    (hproject : DifferentiableOn ℂ project D)
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    DifferentiableOn ℂ (thetaOneFormLinear period project φ) D := by
  apply hproject.clm_apply
  intro x hx
  exact (DerivativeFactorizationAdelicLattice.firstCoefficient_differentiableAt (toDerivativeFactorizationInput φ) (period x)).comp_differentiableWithinAt
    x (hperiod x hx)

/-- The checked finite-trace bridge now applies with an identification
proved by construction (`rfl`), rather than a new substantive hypothesis. -/
theorem canonical_finite_trace
    {I G : Type*} [Fintype I]
    (period : BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (project : BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] Cotangent)
    (finiteInverse : G → PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (pullback : G → (BallCoordinates → Cotangent) →ₗ[ℂ] (BallCoordinates → Cotangent))
    (h_ThetaOneForms : ∀ γ φ,
      pullback γ (thetaOneFormLinear period project φ) =
        thetaOneFormLinear period project (finiteInverse γ φ))
    (representatives : I → G)
    (geometricTrace : (BallCoordinates → Cotangent) →ₗ[ℂ] (BallCoordinates → Cotangent))
    (h_TateComparison : ∀ ω,
      geometricTrace ω = ∑ i, pullback (representatives i) ω)
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    geometricTrace (thetaOneFormLinear period project φ) =
      thetaOneFormLinear period project
        (∑ i, finiteInverse (representatives i) φ) :=
  No.finite_trace_covariance _ (thetaOneFormLinear period project) (fun _ => rfl)
    finiteInverse pullback h_ThetaOneForms representatives geometricTrace h_TateComparison φ

end

end OAI.RepresentationTheory.Theta.Geometric.LinearTheta

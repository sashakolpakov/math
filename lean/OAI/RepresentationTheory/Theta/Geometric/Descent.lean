import OAI.RepresentationTheory.Theta.Geometric.LinearTheta
import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.Descent

noncomputable section

/-!
# Canonical theta forms at a congruence level

Forms on the quotient are represented by invariant holomorphic cotangent
sections on its ball cover. This is the same descent convention as ThetaOneForms.
The input map is constructed from the actual theta series. Rational
covariance is a named ThetaOneForms input; holomorphy and linearity are proved.
-/

open scoped _root_.Matrix.Norms.Elementwise

def restrictForm (D : Set LinearTheta.BallCoordinates) :
    (LinearTheta.BallCoordinates → LinearTheta.Cotangent) →ₗ[ℂ] (D → LinearTheta.Cotangent) where
  toFun ω x := ω x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def holomorphicSections (D : Set LinearTheta.BallCoordinates) : Submodule ℂ (D → LinearTheta.Cotangent) where
  carrier := {ω | ∃ f : LinearTheta.BallCoordinates → LinearTheta.Cotangent,
    DifferentiableOn ℂ f D ∧ ∀ x : D, f x.val = ω x}
  zero_mem' := ⟨0, differentiableOn_const _, fun _ => rfl⟩
  add_mem' := by
    rintro ω η ⟨f, hf, he⟩ ⟨g, hg, he'⟩
    exact ⟨f + g, hf.add hg, fun x => by simp only [Pi.add_apply, he, he']⟩
  smul_mem' := by
    rintro c ω ⟨f, hf, he⟩
    exact ⟨c • f, hf.const_smul c, fun x => by simp only [Pi.smul_apply, he]⟩

variable {GQ : Type*} [Group GQ] [MulAction GQ LinearTheta.BallCoordinates]

/-- Actual cotangent pullback, computed by the derivative of the period action. -/
def cotangentPullback (D : Set LinearTheta.BallCoordinates)
    (hpreserves : ∀ γ : GQ, ∀ x ∈ D, γ • x ∈ D) (γ : GQ) :
    (D → LinearTheta.Cotangent) →ₗ[ℂ] (D → LinearTheta.Cotangent) where
  toFun ω x := (ω ⟨γ • x.val, hpreserves γ x.val x.property⟩).comp
    (fderiv ℂ (fun y : LinearTheta.BallCoordinates => γ • y) x.val)
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

def invariantSections (D : Set LinearTheta.BallCoordinates)
    (hpreserves : ∀ γ : GQ, ∀ x ∈ D, γ • x ∈ D)
    (Γ : Subgroup GQ) : Submodule ℂ (D → LinearTheta.Cotangent) where
  carrier := {ω | ∀ γ ∈ Γ, cotangentPullback D hpreserves γ ω = ω}
  zero_mem' := by intro γ hγ; exact map_zero _
  add_mem' := by intro ω η hω hη γ hγ; simp [hω γ hγ, hη γ hγ]
  smul_mem' := by intro c ω hω γ hγ; simp [hω γ hγ]

def descendedForms (D : Set LinearTheta.BallCoordinates)
    (hpreserves : ∀ γ : GQ, ∀ x ∈ D, γ • x ∈ D)
    (Γ : Subgroup GQ) : Submodule ℂ (D → LinearTheta.Cotangent) :=
  holomorphicSections D ⊓ invariantSections D hpreserves Γ

variable {ι Gf : Type*} [Fintype ι] [Group Gf]

/-- The finite representation is the supplied AdelicTheta splitting composed
with PoissonAutomorphy's actual finite Schrodinger action, not an independent operator. -/
def finiteWeilFromSplitting
    [DecidableEq ι] {MpR MpF MpA : Type*}
    [Group MpR] [Group MpF] [Group MpA]
    (W : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (split : Gf →* MpF) :
    Gf →* (PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] PoissonAutomorphyNormalizationData.finiteSchwartz ι) :=
  W.finite.action.comp split

/-- The spherical input is a submodule of PoissonAutomorphy's actual finite test space. -/
def canonicalSphericalInput
    [DecidableEq ι] (q : ℕ) [Fact q.Prime]
    {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
    (W : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (split : SphericalGU.Spherical.SL3 q →* MpF) :
    Submodule ℂ (PoissonAutomorphyNormalizationData.finiteSchwartz ι) :=
  SphericalGU.Spherical.fixedInputs (SphericalGU.Spherical.integralSL3 q) (finiteWeilFromSplitting W split)

/-- AdelicTheta's local splitting acts through the finite Weil representation on
the same inputs used by the canonical theta construction. -/
def canonicalSphericalWeil
    [DecidableEq ι] (q : ℕ) [Fact q.Prime]
    {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
    (W : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (split : SphericalGU.Spherical.SL3 q →* MpF)
    (T : SphericalGU.Spherical.SL3Hecke q) :
    canonicalSphericalInput q W split →ₗ[ℂ] canonicalSphericalInput q W split :=
  SphericalGU.Spherical.weilAction (SphericalGU.Spherical.integralSL3 q) (finiteWeilFromSplitting W split) T

/-- The canonical map to invariant holomorphic sections. Its linear
identification with ThetaOneForms follows from derivative uniqueness in Theta. -/
def descendedTheta
    (D : Set LinearTheta.BallCoordinates)
    (hpreserves : ∀ γ : GQ, ∀ x ∈ D, γ • x ∈ D)
    (period : LinearTheta.BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (hperiod : DifferentiableOn ℂ (fun x => (period x).matrix) D)
    (project : LinearTheta.BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] LinearTheta.Cotangent)
    (hproject : DifferentiableOn ℂ project D)
    (qf : GQ →* Gf) (rho : Gf →* (PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] PoissonAutomorphyNormalizationData.finiteSchwartz ι))
    (K : Subgroup Gf)
    (h_ThetaOneForms : ∀ γ φ,
      cotangentPullback D hpreserves γ
          (restrictForm D (LinearTheta.thetaOneFormLinear period project (rho (qf γ) φ))) =
        restrictForm D (LinearTheta.thetaOneFormLinear period project φ)) :
    SphericalGU.Spherical.fixedInputs K rho →ₗ[ℂ] descendedForms D hpreserves (K.comap qf) :=
  LinearMap.codRestrict _
    ((restrictForm D).comp ((LinearTheta.thetaOneFormLinear period project).comp
      (SphericalGU.Spherical.fixedInputs K rho).subtype)) (by
      intro φ
      constructor
      · exact ⟨LinearTheta.thetaOneFormLinear period project φ.val,
          LinearTheta.canonical_oneForm_holomorphic D period hperiod project hproject φ.val,
          fun _ => rfl⟩
      · intro γ hγ
        change cotangentPullback D hpreserves γ
            (restrictForm D (LinearTheta.thetaOneFormLinear period project φ.val)) =
          restrictForm D (LinearTheta.thetaOneFormLinear period project φ.val)
        have hfix := φ.property (qf γ) hγ
        simpa only [hfix] using h_ThetaOneForms γ φ.val)

@[simp] theorem descendedTheta_apply
    (D : Set LinearTheta.BallCoordinates)
    (hpreserves : ∀ γ : GQ, ∀ x ∈ D, γ • x ∈ D)
    (period : LinearTheta.BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (hperiod : DifferentiableOn ℂ (fun x => (period x).matrix) D)
    (project : LinearTheta.BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] LinearTheta.Cotangent)
    (hproject : DifferentiableOn ℂ project D)
    (qf : GQ →* Gf) (rho : Gf →* (PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] PoissonAutomorphyNormalizationData.finiteSchwartz ι))
    (K : Subgroup Gf)
    (h_ThetaOneForms : ∀ γ φ,
      cotangentPullback D hpreserves γ
          (restrictForm D (LinearTheta.thetaOneFormLinear period project (rho (qf γ) φ))) =
        restrictForm D (LinearTheta.thetaOneFormLinear period project φ))
    (φ : SphericalGU.Spherical.fixedInputs K rho) (x : D) :
    (descendedTheta D hpreserves period hperiod project hproject qf rho K h_ThetaOneForms φ).val x =
      project x.val (LinearTheta.canonicalFirst φ.val (period x.val)) := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Descent

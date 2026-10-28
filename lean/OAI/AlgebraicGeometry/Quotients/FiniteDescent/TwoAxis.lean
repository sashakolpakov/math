import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PairCohomology
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBoundary
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalCycleDetection

/-! # Two Axis -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TwoAxis

noncomputable section

/-! Two finite free axis detectors lift degree-zero fiber cycles of a
finite free model over a local ring. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Construction.TwoAxisCycleLift

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (D C T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} R))
variable [Module.Finite R D.X₁] [Module.Free R D.X₁]
variable [Module.Finite R D.X₂] [Module.Free R D.X₂]
variable [Module.Finite R D.X₃] [Module.Free R D.X₃]
variable [Module.Finite R Q₁.X₂] [Module.Free R Q₁.X₂]
variable [Module.Finite R Q₂.X₂] [Module.Free R Q₂.X₂]

theorem lift (φ : D ⟶ C) (r₁ : C ⟶ T₁) (r₂ : C ⟶ T₂)
    (p₁ : T₁ ⟶ Q₁) (p₂ : T₂ ⟶ Q₂) (h₁ : Q₁.f = 0) (h₂ : Q₂.f = 0)
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapShortComplex.map φ)]
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapShortComplex.map p₁)]
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapShortComplex.map p₂)]
    (hj : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapShortComplex.map r₂))
    (z : IsLocalRing.ResidueField R ⊗[R] D.X₁)
    (hz : D.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : D.X₁, D.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z := by
  let N := PairCohomology.Construction.PairCohomologyDetector.target (Q₁ := Q₁) (Q₂ := Q₂)
  let b := PairCohomology.Construction.PairCohomologyDetector.map (φ ≫ r₁) (φ ≫ r₂) p₁ p₂
  have : Module.Finite R N := PairCohomology.Construction.PairCohomologyDetector.finite
  have : Module.Free R N := PairCohomology.Construction.PairCohomologyDetector.free
  apply LocalCycleDetection.Construction.LocalSectionLifting.lift_cycle D N b
    (PairCohomology.Construction.PairCohomologyDetector.incoming_zero (φ ≫ r₁) (φ ≫ r₂) p₁ p₂ h₁ h₂) _ z hz
  intro w hw hb
  let a := algebraMap R (IsLocalRing.ResidueField R)
  let F := (ModuleCat.extendScalars a).mapShortComplex
  have hd : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects (F.map (φ ≫ r₁)) (F.map (φ ≫ r₂)) := by
    rw [F.map_comp, F.map_comp]
    exact CechBoundary.Construction.CechBoundaryTransport.jointly_precompose (F.map φ) (F.map r₁) (F.map r₂) hj
  exact PairCohomology.Construction.PairCohomologyDetector.detects (φ ≫ r₁) (φ ≫ r₂) p₁ p₂ a hd w hw hb

end Construction.TwoAxisCycleLift

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TwoAxis

import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TwoAxis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomotopyBoundaryDetection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts

/-! # Model Axis Cycle Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModelAxisCycleLifting

noncomputable section

/-! Finite models of the two axes suffice for local cycle lifting.
The comparison maps run from the models to Cech complexes; no retraction
from a Cech complex to a finite model is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (D T₁ T₂ : ShortComplex (ModuleCat.{u} R))
variable [Module.Finite R D.X₁] [Module.Free R D.X₁]
variable [Module.Finite R D.X₂] [Module.Free R D.X₂]
variable [Module.Finite R D.X₃] [Module.Free R D.X₃]
variable [Module.Finite R T₁.X₁] [Module.Free R T₁.X₁]
variable [Module.Finite R T₁.X₂] [Module.Free R T₁.X₂]
variable [Module.Finite R T₁.X₃] [Module.Free R T₁.X₃]
variable [Module.Finite R T₂.X₁] [Module.Free R T₂.X₁]
variable [Module.Finite R T₂.X₂] [Module.Free R T₂.X₂]
variable [Module.Finite R T₂.X₃] [Module.Free R T₂.X₃]

theorem finiteModel_axes_lift_cycle (r₁ : D ⟶ T₁) (r₂ : D ⟶ T₂)
    (h₁ : ∀ z : IsLocalRing.ResidueField R ⊗[R] T₁.X₁,
      T₁.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0 →
      ∃ x : T₁.X₁, T₁.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z)
    (h₂ : ∀ z : IsLocalRing.ResidueField R ⊗[R] T₂.X₁,
      T₂.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0 →
      ∃ x : T₂.X₁, T₂.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z)
    (hj : Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapShortComplex.map r₂))
    (z : IsLocalRing.ResidueField R ⊗[R] D.X₁)
    (hz : D.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : D.X₁, D.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z := by
  obtain ⟨P₁⟩ := Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.exists_localMinimalShortComplex T₁
  obtain ⟨P₂⟩ := Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.exists_localMinimalShortComplex T₂
  have hf₁ : P₁.complex.f = 0 := ModuleCat.hom_ext (P₁.first_zero_of_residue_cycles_lift h₁)
  have hf₂ : P₂.complex.f = 0 := ModuleCat.hom_ext (P₂.first_zero_of_residue_cycles_lift h₂)
  let F := ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))
  have : ShortComplex.QuasiIso (F.mapShortComplex.map P₁.equivalence.hom) :=
    ⟨(Quotients.FiniteDescent.ShortComplexEndpointHomotopy.Construction.LocalSectionLifting.shortComplexHomotopyEquivMapHomologyIso F P₁.equivalence).isIso_hom⟩
  have : ShortComplex.QuasiIso (F.mapShortComplex.map P₂.equivalence.hom) :=
    ⟨(Quotients.FiniteDescent.ShortComplexEndpointHomotopy.Construction.LocalSectionLifting.shortComplexHomotopyEquivMapHomologyIso F P₂.equivalence).isIso_hom⟩
  exact Quotients.FiniteDescent.TwoAxis.Construction.TwoAxisCycleLift.lift D D T₁ T₂ P₁.complex P₂.complex
    (𝟙 D) r₁ r₂ P₁.equivalence.hom P₂.equivalence.hom hf₁ hf₂ hj z hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModelAxisCycleLifting

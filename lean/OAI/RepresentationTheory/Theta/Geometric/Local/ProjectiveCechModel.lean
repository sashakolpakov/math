import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionAlgebra
import OAI.RepresentationTheory.Theta.Geometric.MinimalNormalizedSections
import Mathlib.RingTheory.LocalRing.Module

/-! # Projective Cech Model -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.ProjectiveCechModel

noncomputable section

/-! A flat projective line-bundle family over a Noetherian local affine
base has an actual universally valid Cech model with a minimal first
three terms. No cohomology model is supplied as an extra input. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {S : Scheme.{u}} [IsAffine S]
    [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
    (X : Over S) (P : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]

include P in
theorem exists_local_projective_cech_model (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    ∃ (C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
      (φ : C ⟶ AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveBaseRingModel.Construction.ProjectiveCechComplex.actualComplex X P L.sheaf),
      QuasiIso φ ∧ Nonempty (AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module Γ(S, ⊤) V],
        QuasiIso (AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map V φ) := by
  obtain ⟨C, φ, hφ, _, hf, hp, ht⟩ :=
    AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveBaseRingModel.Construction.ProjectiveCechComplex.exists_actual_finite_projective X P L
  have : Module.Finite Γ(S, ⊤) (C.X 0) := hf 0
  have : Module.Finite Γ(S, ⊤) (C.X 1) := hf 1
  have : Module.Finite Γ(S, ⊤) (C.X 2) := hf 2
  have : Module.Projective Γ(S, ⊤) (C.X 0) := hp 0
  have : Module.Projective Γ(S, ⊤) (C.X 1) := hp 1
  have : Module.Projective Γ(S, ⊤) (C.X 2) := hp 2
  have : Module.Free Γ(S, ⊤) (C.X 0) := Module.free_of_flat_of_isLocalRing
  have : Module.Free Γ(S, ⊤) (C.X 1) := Module.free_of_flat_of_isLocalRing
  have : Module.Free Γ(S, ⊤) (C.X 2) := Module.free_of_flat_of_isLocalRing
  have : Module.Finite Γ(S, ⊤) (C.sc' 0 1 2).X₁ := hf 0
  have : Module.Finite Γ(S, ⊤) (C.sc' 0 1 2).X₂ := hf 1
  have : Module.Finite Γ(S, ⊤) (C.sc' 0 1 2).X₃ := hf 2
  have : Module.Free Γ(S, ⊤) (C.sc' 0 1 2).X₁ := inferInstanceAs (Module.Free Γ(S, ⊤) (C.X 0))
  have : Module.Free Γ(S, ⊤) (C.sc' 0 1 2).X₂ := inferInstanceAs (Module.Free Γ(S, ⊤) (C.X 1))
  have : Module.Free Γ(S, ⊤) (C.sc' 0 1 2).X₃ := inferInstanceAs (Module.Free Γ(S, ⊤) (C.X 2))
  exact ⟨C, φ, hφ, AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.exists_localMinimalShortComplex (C.sc' 0 1 2), ht⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Local.ProjectiveCechModel

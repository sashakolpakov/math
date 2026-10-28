import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedLocalFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

/-! # Normalized Frame Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedFrameCover

noncomputable section

/-! An actual line bundle trivialized on the reduced fiber has a
constructed affine cover of normalized local frames. Its reduced opens
cover the original scheme, and its frame opens cover the whole family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

structure NormalizedDualFrame where
  domain : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens
  affine : IsAffineOpen domain
  frame : (Scheme.Modules.pullback domain.ι).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule domain.toScheme
  reduces : Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X domain) frame = NormalizedLocalFrames.prescribedReducedLocalFrame X e₀ domain

def NormalizedDualFrame.baseOpen (a : NormalizedDualFrame X L e₀) : X.left.Opens :=
  (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ a.domain

theorem NormalizedDualFrame.baseOpen_affine (a : NormalizedDualFrame X L e₀) :
    IsAffineOpen (a.baseOpen X L e₀) := ReductionOpens.dualAffineOpen_reduction X a.domain a.affine

def NormalizedDualFrame.localFrame (a : NormalizedDualFrame X L e₀) : LineFrameAtlas.LocalLineFrame L.sheaf :=
  ⟨a.domain, (Scheme.Modules.restrictFunctorIsoPullback a.domain.ι).app L.sheaf ≪≫ a.frame⟩

theorem exists_normalizedDualFrame (x : X.left) :
    ∃ a : NormalizedDualFrame X L e₀, x ∈ a.baseOpen X L e₀ := by
  obtain ⟨U, hx, hU, _, e, he⟩ := NormalizedLocalFrames.exists_affine_normalized_dual_frame X L e₀ x
  exact ⟨⟨U, hU, e, he⟩, hx⟩

def normalizedDualFrameAt (x : X.left) : NormalizedDualFrame X L e₀ :=
  (exists_normalizedDualFrame X L e₀ x).choose

theorem normalizedDualFrameAt_mem (x : X.left) :
    x ∈ (normalizedDualFrameAt X L e₀ x).baseOpen X L e₀ :=
  (exists_normalizedDualFrame X L e₀ x).choose_spec

theorem normalizedDualFrameCover_base :
    (⨆ x : X.left, (normalizedDualFrameAt X L e₀ x).baseOpen X L e₀) = ⊤ := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, normalizedDualFrameAt_mem X L e₀ x⟩

theorem normalizedDualFrameCover_family :
    (⨆ x : X.left, (normalizedDualFrameAt X L e₀ x).domain) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective X).surj y
  exact Opens.mem_iSup.mpr ⟨x, normalizedDualFrameAt_mem X L e₀ x⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedFrameCover

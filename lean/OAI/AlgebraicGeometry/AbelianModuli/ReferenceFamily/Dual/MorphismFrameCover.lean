import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MorphismOpenReductionSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.FramePullbackCube
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedFrameCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedOpenFrameConverse

/-! # Morphism Frame Cover -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual

/-! Pullback of an original normalized dual-family frame is an
actual normalized frame on every compatible affine source open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ Y).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y.left)
    (a : NormalizedFrameCover.NormalizedDualFrame Y L e₀) (V : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (h : V ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ a.domain)

theorem MorphismFrameCover.dualMorphismFrame_normalized :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X V)
      (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left V.ι a.domain.ι
        ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.resLE a.domain V h)
        (Scheme.Hom.resLE_comp_ι _ h) L.sheaf a.frame) =
      NormalizedLocalFrames.prescribedReducedLocalFrame X (DualLine.KernelMorphism.dualMorphismReductionFrame f L e₀) V := by
  apply ReducedOpenFrameConverse.reducedOpenFrame_of_chart (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left
    (DualLine.KernelMorphism.dualMorphismReductionFrame f L e₀) V _
  have he : RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left ⁻¹ᵁ a.domain).ι a.domain.ι
      (DualOpen.Product.dualOpenReduction Y a.domain) (DualOpen.Product.dualOpenReduction_ι Y a.domain) L.sheaf a.frame =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left ⁻¹ᵁ a.domain).ι e₀ :=
    (ReducedFrame.reducedOpenFrame_chart (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left e₀ a.domain a.frame a.reduces).trans
      (ReducedFrame.nativePullbackFrame_agrees _ e₀).symm
  have H := Normalized.FramePullbackCube.normalizedFrame_pullback_cube (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left f.left
    (congrArg Over.Hom.left (DualLine.KernelMorphism.dualFamilyMorphism_reduction f).symm)
    V.ι a.domain.ι ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.resLE a.domain V h)
    (Scheme.Hom.resLE_comp_ι _ h)
    ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).ι
    ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left ⁻¹ᵁ a.domain).ι
    (MorphismOpenReductionSquare.dualMorphismReducedOpen f a.domain V h).left
    (congrArg Over.Hom.left (MorphismOpenReductionSquare.dualMorphismReducedOpen_inclusion f a.domain V h))
    (DualOpen.Product.dualOpenReduction X V) (DualOpen.Product.dualOpenReduction Y a.domain)
    (DualOpen.Product.dualOpenReduction_ι X V) (DualOpen.Product.dualOpenReduction_ι Y a.domain)
    (MorphismOpenReductionSquare.dualMorphismOpenReduction_square f a.domain V h) L.sheaf e₀ a.frame he
  exact H.trans (ReducedFrame.nativePullbackFrame_agrees _ (DualLine.KernelMorphism.dualMorphismReductionFrame f L e₀))

def NormalizedFrameCover.NormalizedDualFrame.morphismPullback (hV : IsAffineOpen V) :
    NormalizedFrameCover.NormalizedDualFrame X (L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left)
      (DualLine.KernelMorphism.dualMorphismReductionFrame f L e₀) where
  domain := V
  affine := hV
  frame := RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left V.ι a.domain.ι
    ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.resLE a.domain V h) (Scheme.Hom.resLE_comp_ι _ h) L.sheaf a.frame
  reduces := MorphismFrameCover.dualMorphismFrame_normalized f L e₀ a V h

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MorphismFrameCover

/-! Every original normalized target frame cover constructs an actual
compatible affine source frame cover for the pulled dual-family bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ Y).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y.left) {I : Type} (s : I → NormalizedFrameCover.NormalizedDualFrame Y L e₀)

structure DualMorphismFrameIndex where
  target : I
  chart : (LieRanks.dualNumberTest ℂ ⊗ X).left.affineOpens
  target_le : chart.1 ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ (s target).domain

def dualMorphismCoverFrame (i : DualMorphismFrameIndex f L e₀ s) :
    NormalizedFrameCover.NormalizedDualFrame X (L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left)
      (DualLine.KernelMorphism.dualMorphismReductionFrame f L e₀) :=
  NormalizedFrameCover.NormalizedDualFrame.morphismPullback f L e₀ (s i.target) i.chart.1 i.target_le i.chart.2

theorem dualMorphismCoverFrame_covers (hs : iSup (fun i => (s i).baseOpen Y L e₀) = ⊤) :
    iSup (fun i : DualMorphismFrameIndex f L e₀ s =>
      (dualMorphismCoverFrame f L e₀ s i).baseOpen X _ _) = ⊤ := by
  apply top_unique
  intro x _
  have hy : f.left x ∈ iSup (fun i => (s i).baseOpen Y L e₀) := by rw [hs]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  have hp : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x ∈
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ (s i).domain := by
    have H := congrArg (fun q : X ⟶ LieRanks.dualNumberTest ℂ ⊗ Y => q.left x) (DualLine.KernelMorphism.dualFamilyMorphism_reduction f)
    change (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x) =
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left (f.left x) at H
    change (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x) ∈ (s i).domain
    rw [H]
    exact hi
  obtain ⟨V, hV, hxV, hsub⟩ := exists_isAffineOpen_mem_and_subset hp
  exact Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV⟩, hsub⟩, hxV⟩

theorem dualMorphismCoverFrame_refines (i : DualMorphismFrameIndex f L e₀ s) :
    (dualMorphismCoverFrame f L e₀ s i).baseOpen X _ _ ≤
      f.left ⁻¹ᵁ (s i.target).baseOpen Y L e₀ :=
  MorphismOpenReductionSquare.dualMorphismReducedOpen_le f (s i.target).domain i.chart.1 i.target_le

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MorphismFrameCover

end

end OAI

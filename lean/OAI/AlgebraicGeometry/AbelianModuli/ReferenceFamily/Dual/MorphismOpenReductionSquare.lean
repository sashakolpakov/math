import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.KernelMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Product

/-! # Morphism Open Reduction Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MorphismOpenReductionSquare

noncomputable section

section

/-! Compatible original dual-family opens induce a literal map
between their reduced open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (U : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens) (V : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (h : V ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U)

include h

theorem dualMorphismReducedOpen_le :
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V ≤
      f.left ⁻¹ᵁ ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left ⁻¹ᵁ U) := by
  intro x hx
  have H := congrArg (fun q : X ⟶ LieRanks.dualNumberTest ℂ ⊗ Y => q.left x) (DualLine.KernelMorphism.dualFamilyMorphism_reduction f)
  change (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x) =
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left (f.left x) at H
  change (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left (f.left x) ∈ U
  exact H ▸ h hx

def dualMorphismReducedOpen : DualOpen.Product.dualReducedOpenOver X V ⟶ DualOpen.Product.dualReducedOpenOver Y U :=
  Over.homMk (f.left.resLE _ _ (dualMorphismReducedOpen_le f U V h)) (by
    change (f.left.resLE _ _ _ ≫ ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left ⁻¹ᵁ U).ι) ≫ Y.hom = _
    rw [Scheme.Hom.resLE_comp_ι, Category.assoc, f.w]
    rfl)

theorem dualMorphismReducedOpen_inclusion :
    dualMorphismReducedOpen f U V h ≫ DualOpen.Product.dualReducedOpenInclusion Y U =
      DualOpen.Product.dualReducedOpenInclusion X V ≫ f := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι _ _

theorem dualMorphismOpenProduct_square :
    DualOpen.Product.dualOpenProductMap X V ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left =
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ dualMorphismReducedOpen f U V h).left ≫ DualOpen.Product.dualOpenProductMap Y U := by
  change ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ DualOpen.Product.dualReducedOpenInclusion X V) ≫
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f)).left =
    ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ dualMorphismReducedOpen f U V h) ≫
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ DualOpen.Product.dualReducedOpenInclusion Y U)).left
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, dualMorphismReducedOpen_inclusion]

end

/-! Restricting the actual dual-family reduction square to compatible
opens gives the same original reduced-open morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

attribute [local implicit_reducible] DualOpen.Product.dualReducedOpenOver

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (U : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens) (V : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (h : V ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U)

theorem dualMorphismOpenReduction_square :
    DualOpen.Product.dualOpenReduction X V ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.resLE U V h =
      (dualMorphismReducedOpen f U V h).left ≫ DualOpen.Product.dualOpenReduction Y U := by
  apply (cancel_mono U.ι).mp
  have hg : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left =
      f.left ≫ (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left :=
    congrArg Over.Hom.left (DualLine.KernelMorphism.dualFamilyMorphism_reduction f)
  have hi : (dualMorphismReducedOpen f U V h).left ≫
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left ⁻¹ᵁ U).ι =
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).ι ≫ f.left :=
    congrArg Over.Hom.left (dualMorphismReducedOpen_inclusion f U V h)
  have hl : (DualOpen.Product.dualOpenReduction X V ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.resLE U V h) ≫ U.ι =
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).ι ≫
        (f.left ≫ (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left) := by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, DualOpen.Product.dualOpenReduction_ι,
      Category.assoc, hg]
  have hr : ((dualMorphismReducedOpen f U V h).left ≫ DualOpen.Product.dualOpenReduction Y U) ≫ U.ι =
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ V).ι ≫
        (f.left ≫ (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left) := by
    rw [Category.assoc, DualOpen.Product.dualOpenReduction_ι, ← Category.assoc, hi, Category.assoc]
  exact hl.trans hr.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MorphismOpenReductionSquare

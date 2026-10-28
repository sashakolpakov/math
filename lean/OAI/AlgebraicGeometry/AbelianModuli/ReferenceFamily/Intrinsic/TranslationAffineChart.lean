import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientProductChart
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualMapReductionSquare

/-! # Translation Affine Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart

noncomputable section

section

/-! The original affine coefficient chart for infinitesimal
translation is the product of the original affine open immersion with
the dual-number test, through the constructed coefficient isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G)

theorem dualAffineTranslationChart_factor :
    InfinitesimalTranslation.dualAffineTranslationChart G B i = Dual.CoefficientProductChart.dualCoefficientProductMap B ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ i) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [InfinitesimalTranslation.dualAffineTranslationChart, Dual.CoefficientProductChart.dualCoefficientProductMap, Category.assoc,
      tensorHom_fst, Category.comp_id, lift_fst]
  · simp only [InfinitesimalTranslation.dualAffineTranslationChart, Dual.CoefficientProductChart.dualCoefficientProductMap, Category.assoc,
      tensorHom_snd, lift_snd, lift_snd_assoc]
    change Dual.CoefficientSchemeTests.dualCoefficientProjection ℂ B ≫ Affine.ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i =
      Dual.CoefficientSchemeTests.dualCoefficientProjection ℂ B ≫ i
    unfold Affine.ChartCoefficientConormal.affineChartCoefficientPoint
    rw [Affine.SelfLiftDerivations.affineOverAlgHom_self, Category.id_comp]

instance dualAffineTranslationChart_open [IsOpenImmersion i.left] :
    IsOpenImmersion (InfinitesimalTranslation.dualAffineTranslationChart G B i).left := by
  have ht : IsOpenImmersion (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ i).left :=
    Picard.PoincareBundle.Product.Covers.property_tensor (@IsOpenImmersion) (𝟙 (LieRanks.dualNumberTest ℂ)) i
      (by change IsOpenImmersion (𝟙 (LieRanks.dualNumberTest ℂ).left); infer_instance) inferInstance
  rw [dualAffineTranslationChart_factor, Over.comp_left]
  exact IsOpenImmersion.comp _ _

end

/-! The actual affine translation coefficient chart has precisely
the inverse image of the original affine open under projection.
The proof uses the original surjective dual-number reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y) [IsOpenImmersion i.left]

omit [IsOpenImmersion i.left] in
theorem dualProductOpenRange :
    Set.range (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ i).left =
      (snd (LieRanks.dualNumberTest ℂ) Y).left ⁻¹' Set.range i.left := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(snd (LieRanks.dualNumberTest ℂ) X).left x, ?_⟩
    exact (congrArg (fun f : LieRanks.dualNumberTest ℂ ⊗ X ⟶ Y => f.left x)
      (tensorHom_snd (𝟙 (LieRanks.dualNumberTest ℂ)) i)).symm
  · obtain ⟨x, rfl⟩ := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective Y).surj y
    intro hy
    have hp := congrArg (fun f : Y ⟶ Y => f.left x) (Dual.ReductionOpens.dualBaseChangeReduction_projection Y)
    change (snd (LieRanks.dualNumberTest ℂ) Y).left ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left x) = x at hp
    change (snd (LieRanks.dualNumberTest ℂ) Y).left ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left x) ∈ Set.range i.left at hy
    rw [hp] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨(RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left z, ?_⟩
    exact (congrArg (fun f : X ⟶ LieRanks.dualNumberTest ℂ ⊗ Y => f.left z)
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_natural i)).trans
        (congrArg (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left hz)

theorem dualAffineTranslationChart_range (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B : CommAlgCat ℂ)
    (j : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion j.left] :
    (InfinitesimalTranslation.dualAffineTranslationChart G B j).left.opensRange =
      (snd (LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ j.left.opensRange := by
  apply TopologicalSpace.Opens.ext
  change Set.range (InfinitesimalTranslation.dualAffineTranslationChart G B j).left =
    (snd (LieRanks.dualNumberTest ℂ) G).left ⁻¹' Set.range j.left
  rw [dualAffineTranslationChart_factor, Over.comp_left]
  change Set.range ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ j).left ∘ (Dual.CoefficientProductChart.dualCoefficientProductMap B).left) = _
  have hs : Function.Surjective (Dual.CoefficientProductChart.dualCoefficientProductMap B).left :=
    (inferInstance : Surjective (Dual.CoefficientProductChart.dualCoefficientProductMap B).left).surj
  rw [Set.range_comp, hs.range_eq, Set.image_univ]
  exact dualProductOpenRange j

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart

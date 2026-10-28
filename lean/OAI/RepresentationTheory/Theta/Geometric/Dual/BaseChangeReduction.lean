import OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers

/-! # Base Change Reduction -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction

noncomputable section

/-! The actual reduction of a dual-number base change is surjective on
underlying points and preserves every morphism and constant point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

def dualBaseChangeReduction (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) : X ⟶ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X :=
  lift (toUnit X ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ) (𝟙 X)

theorem dualBaseChangeReduction_natural {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    dualBaseChangeReduction X ≫ (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f) =
      f ≫ dualBaseChangeReduction Y := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [dualBaseChangeReduction]

theorem dualBaseChangeReduction_surjective (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    Surjective (dualBaseChangeReduction X).left := by
  let : Surjective (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).left := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberSpectrum.dualNumberOrigin_surjective
  let : Surjective (Over.Hom.left (𝟙 X)) := inferInstanceAs (Surjective (𝟙 X.left))
  let : Surjective (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ⊗ₘ 𝟙 X).left :=
    AlgebraicGeometry.Picard.PoincareBundle.Product.Covers.tensorSurjective (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ) (𝟙 X)
  have H : (λ_ X).inv ≫ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ⊗ₘ 𝟙 X) = dualBaseChangeReduction X := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [dualBaseChangeReduction]
  have hi : Surjective (Over.Hom.left (λ_ X).inv) := by
    change Surjective ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso (λ_ X)).inv
    infer_instance
  have hc : Surjective ((λ_ X).inv.left ≫ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ⊗ₘ 𝟙 X).left) :=
    ⟨(Surjective.surj (f := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ⊗ₘ 𝟙 X).left)).comp hi.surj⟩
  exact (congrArg Over.Hom.left H) ▸ hc

theorem dualConstantPoint_reduction (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ AffineBaseChangeChart.dualConstantPoint X p = p ≫ dualBaseChangeReduction X := by
  have hu : toUnit (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) = 𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) := rfl
  apply CartesianMonoidalCategory.hom_ext <;> simp [AffineBaseChangeChart.dualConstantPoint, dualBaseChangeReduction, hu]

theorem dualBaseChange_range_open {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (U : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens)
    (hf : Set.range (f ≫ dualBaseChangeReduction Y).left ⊆ U) :
    (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) ≤
      (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U := by
  intro y _
  obtain ⟨x, rfl⟩ := (dualBaseChangeReduction_surjective X).surj y
  apply hf
  refine ⟨x, ?_⟩
  exact (congrArg (fun g : X ⟶ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ Y => g.left x)
    (dualBaseChangeReduction_natural f)).symm

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction

import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.MorphismCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureCechRefinedPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism

/-! # Cech Morphism Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechMorphismCoefficients

noncomputable section

/-! The original coefficient equivalences on Cech intersections
commute with actual family pullback and the chosen cover refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ Y).left))]
    (f : X ⟶ Y) {I J : Type}
    (U : I → (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens) (V : J → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (r : J → I) (h : ∀ j, V j ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U (r j))
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))

theorem dualCechSectionCoefficientEquiv_morphism {n : ℕ} (a : Fin (n + 1) → J)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ Y).left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a))) :
    CechCoefficient.dualCechSectionCoefficientEquiv X V hV a
      ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a)
        (StructureCechRefinedPullback.cechMorphismIntersection_le (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left U V r h a) s) =
      NumberCoefficients.dualNumberRingMap (f.left.appLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover Y U) (r ∘ a))
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover X V) a)
        (StructureCechRefinedPullback.cechMorphismIntersection_le f.left (CechCoefficient.dualReducedCechCover Y U) (CechCoefficient.dualReducedCechCover X V) r
          (fun j => MorphismOpenReductionSquare.dualMorphismReducedOpen_le f (U (r j)) (V j) (h j)) a)).hom
            (CechCoefficient.dualCechSectionCoefficientEquiv Y U hU (r ∘ a) s) := by
  change NumberCoefficients.dualNumberRingMap (Regular.SectionTransport.regularSectionTransport (CechCoefficient.dualReducedCechIntersection X V a)).toRingHom
      (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a) (CechCoefficient.dualCechIntersection_affine X V hV a)
        ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE _ _ _ s)) = _
  rw [DualOpen.MorphismCoefficients.dualOpenSectionCoefficientEquiv_morphism f (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a)
    (StructureCechRefinedPullback.cechMorphismIntersection_le (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left U V r h a)
    (CechCoefficient.dualCechIntersection_affine Y U hU (r ∘ a)) (CechCoefficient.dualCechIntersection_affine X V hV a)]
  apply TrivSqZeroExt.ext
  · exact Affine.PresentationSectionMorphism.regularSectionTransport_appLE f.left (CechCoefficient.dualReducedCechIntersection Y U (r ∘ a))
      (CechCoefficient.dualReducedCechIntersection X V a) _ _ _
  · exact Affine.PresentationSectionMorphism.regularSectionTransport_appLE f.left (CechCoefficient.dualReducedCechIntersection Y U (r ∘ a))
      (CechCoefficient.dualReducedCechIntersection X V a) _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechMorphismCoefficients

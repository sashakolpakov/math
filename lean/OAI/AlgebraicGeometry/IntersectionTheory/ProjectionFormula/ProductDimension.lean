import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Product Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension

noncomputable section

/-! The relative dimensions of the projections and the product are
obtained from the genuine product universal property by base change. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

theorem fst_relativeDimension {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (P : ProperCycleLinearity.ProductPresentation X Y) (n : ℕ) [SmoothOfRelativeDimension n Y.structureMap] :
    SmoothOfRelativeDimension n P.fst.left := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk P.fst P.snd) P.isLimit).flip
    (inferInstance : SmoothOfRelativeDimension n Y.structureMap)

theorem relativeDimension {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (P : ProperCycleLinearity.ProductPresentation X Y) (m n : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap] :
    SmoothOfRelativeDimension (m + n) P.space.structureMap := by
  let : SmoothOfRelativeDimension n P.fst.left := fst_relativeDimension P n
  have h : SmoothOfRelativeDimension (n + m) (P.fst.left ≫ X.structureMap) :=
    smoothOfRelativeDimension_comp n m P.fst.left X.structureMap
  have hw : P.fst.left ≫ X.structureMap = P.space.structureMap := P.fst.w
  rw [hw, Nat.add_comm n m] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension

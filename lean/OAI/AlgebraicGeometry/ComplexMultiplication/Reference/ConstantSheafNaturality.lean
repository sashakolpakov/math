import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantPullback

/-! # Constant Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantSheafNaturality

noncomputable section

/-! # Naturality of the original constant-to-holomorphic sheaf map

The actual coefficient identity and actual pullback of holomorphic zero-forms
commute with the unchanged original inclusion of constant sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- The original constant-to-zero-form sheaf map commutes with actual scheme pullback. -/
theorem originalDeRhamSheafPullback_constants (f : X ⟶ Y) :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) ≫
        DeRhamSheafPullback.originalDeRhamSheafPullback f 0 =
      ConstantPullback.originalConstantSheafPullback f (AddCommGrpCat.of ℂ) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    _ _ ((TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 0)).property
  change toSheafify _ (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))
        (AddCommGrpCat.of ℂ)) ≫
      sheafifyMap _ (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left)) ≫
        DeRhamSheafPullback.originalDeRhamSheafPullbackHom f 0 =
    toSheafify _ (AlgebraicTopology.Sheaf.Constant.TopCat.Presheaf.const (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))
        (AddCommGrpCat.of ℂ)) ≫
      ConstantPullback.originalConstantSheafPullbackHom f (AddCommGrpCat.of ℂ) ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (sheafifyMap _ (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    DeRhamSheafPullback.originalDeRhamSheafPullback_unit, ← Category.assoc,
    ConstantPullback.originalDeRhamPresheafPullback_constants, Category.assoc,
    ← Functor.map_comp, toSheafify_naturality, Functor.map_comp,
    ← Category.assoc, ← ConstantPullback.originalConstantSheafPullback_unit]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantSheafNaturality

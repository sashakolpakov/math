import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamPresheafPullback
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # De Rham Sheaf Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamSheafPullback

noncomputable section

/-! # Actual pullback on the original holomorphic de Rham sheaves

The genuine presheaf pullback extends uniquely to the original degreewise
sheafifications. Exterior differentiation still commutes with this extension.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

instance originalSheafPushforward_preservesZeroMorphisms (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).PreservesZeroMorphisms where
  map_zero _ _ := CategoryTheory.Sheaf.hom_ext rfl

/-- The genuine pullback map on the underlying degreewise sheafifications. -/
def originalDeRhamSheafPullbackHom (f : X ⟶ Y) (p : ℕ) :
    sheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p) ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        (sheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p)) :=
  sheafifyLift (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    (DeRhamPresheafPullback.originalDeRhamPresheafPullback f p ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p)))
    ((TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p)).property

/-- Extension of actual form pullback to the original sheafifications. -/
def originalDeRhamSheafPullback (f : X ⟶ Y) (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p) :=
  ⟨originalDeRhamSheafPullbackHom f p⟩

/-- Sheaf pullback extends precisely the actual map on the original form presheaves. -/
theorem originalDeRhamSheafPullback_unit (f : X ⟶ Y) (p : ℕ) :
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p) ≫
      originalDeRhamSheafPullbackHom f p =
    DeRhamPresheafPullback.originalDeRhamPresheafPullback f p ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p)) :=
  toSheafify_sheafifyLift _ _ _

/-- Actual sheaf pullback commutes with the original exterior differential. -/
theorem originalDeRhamSheafPullback_differential (f : X ⟶ Y) (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p ≫
        originalDeRhamSheafPullback f (p + 1) =
      originalDeRhamSheafPullback f p ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    _ _ ((TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (p + 1))).property
  change toSheafify _ (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p) ≫
      sheafifyMap _ (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p) ≫
        originalDeRhamSheafPullbackHom f (p + 1) =
    toSheafify _ (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p) ≫
      originalDeRhamSheafPullbackHom f p ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
          (sheafifyMap _ (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    originalDeRhamSheafPullback_unit, ← Category.assoc,
    DeRhamPresheafPullback.originalDeRhamPresheafPullback_differential, Category.assoc,
    ← Functor.map_comp, toSheafify_naturality, Functor.map_comp,
    ← Category.assoc, ← originalDeRhamSheafPullback_unit]
  exact Category.assoc _ _ _

/-- Actual scheme maps induce a morphism of the original sheaf de Rham complexes. -/
def originalDeRhamSheafComplexPullback (f : X ⟶ Y) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) where
  f p := originalDeRhamSheafPullback f p
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex_d,
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex_d]
    exact (originalDeRhamSheafPullback_differential f i).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamSheafPullback

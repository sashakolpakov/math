import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamPresheafPullback
import OAI.AlgebraicGeometry.Cohomology.GlobalSections
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Analytic Inverse Image -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AnalyticInverseImage

noncomputable section

/-! # Exact inverse image on the original analytic sheaves

Inverse image under the genuine scheme-point map is exact. It transports
the actual constant integer complex to the corresponding original complex
on the source, giving the functorial map needed for original hypercohomology.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- Genuine inverse image of abelian-group sheaves for the original analytic point map. -/
def originalAnalyticSheafInverseImage (f : X ⟶ Y) :
    ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y ⥤ ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X :=
  TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)

/-- Preimage preserves finite intersections of opens, so its comma categories are cofiltered. -/
instance originalAnalyticOpensMap_flat (f : X ⟶ Y) :
    RepresentablyFlat (Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)) where
  cofiltered A := by
    have hnonempty : Nonempty (StructuredArrow A (Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f))) :=
      ⟨StructuredArrow.mk (Y := (⊤ : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))))
        (homOfLE (show A ≤ (Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj ⊤ from
          fun _ _ => trivial))⟩
    let : IsCofilteredOrEmpty (StructuredArrow A (Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f))) := {
      cone_objs := fun U V => by
        let W : StructuredArrow A (Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)) :=
          StructuredArrow.mk (Y := U.right ⊓ V.right)
            (homOfLE (show A ≤ (Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
              (U.right ⊓ V.right) from fun x hx => ⟨leOfHom U.hom hx, leOfHom V.hom hx⟩))
        exact ⟨W, StructuredArrow.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _),
          StructuredArrow.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _), trivial⟩
      cone_maps := fun U _ g h =>
        ⟨U, 𝟙 U, StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)⟩ }
    exact { nonempty := hnonempty }

instance originalAnalyticOpensMap_continuous (f : X ⟶ Y) :
    (Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).IsContinuous
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)
  · exact coverPreserving_opens_map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)

instance originalAnalyticSheafInverseImage_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (originalAnalyticSheafInverseImage f) := by
  change PreservesFiniteLimits
    ((Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).sheafPullback AddCommGrpCat
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))))
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map (DeRhamPresheafPullback.originalAnalyticSchemeMap f)) AddCommGrpCat
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))

instance originalAnalyticSheafInverseImage_preservesFiniteColimits (f : X ⟶ Y) :
    PreservesFiniteColimits (originalAnalyticSheafInverseImage f) :=
  inferInstanceAs (PreservesFiniteColimits
    (TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)))

instance originalAnalyticSheafInverseImage_additive (f : X ⟶ Y) :
    (originalAnalyticSheafInverseImage f).Additive := by
  exact (leftExactFunctor_le_additiveFunctor _ _) _
    (show PreservesFiniteLimits (originalAnalyticSheafInverseImage f) from inferInstance)

/-- Constant sheaves are transported by the actual inverse-image functor. -/
def originalAnalyticConstantInverseImageIso (f : X ⟶ Y) :
    AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) ⋙
        originalAnalyticSheafInverseImage f ≅
      AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    AddCommGrpCat isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f))).leftAdjointUniq
          (constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
            AddCommGrpCat isTerminalTop)

/-- The actual exact functor of original sheaf complexes preserves quasi-isomorphisms. -/
def originalAnalyticInverseImageLocalizer (f : X ⟶ Y) :
    LocalizerMorphism (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms Y) (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) :=
  (originalAnalyticSheafInverseImage f).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)

/-- The original constant integer complex is retained under actual analytic inverse image. -/
def originalIntegerComplexInverseImageIso (f : X ⟶ Y) :
    ((originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y) ≅ ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X :=
  ((originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle Y) ≪≫
    ((originalAnalyticSheafInverseImage f).mapCochainComplexSingleFunctor 0).app
      ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj (AddCommGrpCat.of ℤ)) ≪≫
    (CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).mapIso
      ((originalAnalyticConstantInverseImageIso f).app (AddCommGrpCat.of ℤ)) ≪≫
    (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AnalyticInverseImage

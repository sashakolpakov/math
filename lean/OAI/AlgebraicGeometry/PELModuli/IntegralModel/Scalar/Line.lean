import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Line -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.Line

noncomputable section

section

/-! Equality of actual line-bundle classes along a fixed relation
persists under literal scalar change of both relation arrows. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem lineBundle_scalar_relation_class {S T : Scheme.{0}} (b : T ⟶ S)
    {W X : Over S} (s t : W ⟶ X) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass s.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback b).map s).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst X.hom b))) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback b).map t).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst X.hom b))) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback b).map s).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst X.hom b) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback b).map t).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst X.hom b) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    Cartesian.FamilyMorphismComparison.over_pullback_map_fst b s, Cartesian.FamilyMorphismComparison.over_pullback_map_fst b t,
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h]

end

section

/-! The literal total-space projection from a scalar-changed scheme
is natural on the original slice category. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def scalarTotalProjection {S T : Scheme.{0}} (b : T ⟶ S) :
    Over.pullback b ⋙ Over.map b ⟶ 𝟭 (Over S) where
  app X := Over.homMk (pullback.fst X.hom b) pullback.condition
  naturality _ _ _f := Over.OverMorphism.ext (pullback.lift_fst _ _ _)

theorem scalarTotalProjection_left {S T : Scheme.{0}} (b : T ⟶ S) (X : Over S) :
    (scalarTotalProjection b |>.app X).left = pullback.fst X.hom b := rfl

end

/-! Maps into a literal scalar pullback are determined by their maps
to the original parameter, because the new coefficient structure is fixed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S S' : Scheme.{0}} (b : S' ⟶ S) {T : Over S'} {X Q : Over S}

def scalarOriginalMap (f : T ⟶ (Over.pullback b).obj X) : (Over.map b).obj T ⟶ X :=
  (Over.map b).map f ≫ (scalarTotalProjection b).app X

theorem scalarOriginalMap_left (f : T ⟶ (Over.pullback b).obj X) :
    (scalarOriginalMap b f).left = f.left ≫ pullback.fst X.hom b := rfl

theorem scalarOriginalMap_comp (f : T ⟶ (Over.pullback b).obj X) (π : X ⟶ Q) :
    scalarOriginalMap b (f ≫ (Over.pullback b).map π) = scalarOriginalMap b f ≫ π := by
  apply Over.OverMorphism.ext
  change (f.left ≫ ((Over.pullback b).map π).left) ≫ pullback.fst Q.hom b =
    (f.left ≫ pullback.fst X.hom b) ≫ π.left
  rw [Category.assoc, Cartesian.FamilyMorphismComparison.over_pullback_map_fst, ← Category.assoc]

theorem scalarOriginalMap_injective :
    Function.Injective (scalarOriginalMap b (T := T) (X := X)) := by
  intro f g h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg Over.Hom.left h
  · exact f.w.trans g.w.symm

theorem scalarQuotient_eq_iff (π : X ⟶ Q) (f g : T ⟶ (Over.pullback b).obj X) :
    f ≫ (Over.pullback b).map π = g ≫ (Over.pullback b).map π ↔
      scalarOriginalMap b f ≫ π = scalarOriginalMap b g ≫ π := by
  rw [← scalarOriginalMap_comp, ← scalarOriginalMap_comp]
  exact (scalarOriginalMap_injective b).eq_iff.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.Line

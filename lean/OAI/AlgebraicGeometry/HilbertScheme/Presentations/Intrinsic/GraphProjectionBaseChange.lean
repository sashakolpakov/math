import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CartesianMorphismIsomorphismComparison

/-! # Graph Projection Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphProjectionBaseChange.Hom

noncomputable section

/-! The native graph projection has the actual Cartesian relative
base-change isomorphism condition, including on nonreduced test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S)

theorem subschemeProjection_familyProjection {B : Over S}
    (I : (Hilbert.Functor.ambient (X ⨯ Y) B).IdealSheafData) :
    (GraphLocus.Hom.subschemeProjection X Y I).left ≫ Hilbert.Functor.ambientProjection X B =
      Hilbert.Functor.familyProjection (X ⨯ Y) I := by
  change (I.subschemeι ≫ (HomFunctor.Hom.graphProjection X Y B).left) ≫
    (prod.fst : B ⨯ X ⟶ B).left = I.subschemeι ≫ (prod.fst : B ⨯ (X ⨯ Y) ⟶ B).left
  rw [Category.assoc, ← Over.comp_left]
  simp only [HomFunctor.Hom.graphProjection, prod.map_fst, Category.comp_id]

theorem subschemeProjection_baseChange {T B : Over S} (a : T ⟶ B)
    (I : (Hilbert.Functor.ambient (X ⨯ Y) B).IdealSheafData) :
    (GraphLocus.Hom.subschemeProjection X Y (I.comap (Hilbert.Functor.ambientMap (X ⨯ Y) a))).left ≫
        Hilbert.Functor.ambientMap X a =
      Hilbert.Functor.familyMap (X ⨯ Y) a I ≫ (GraphLocus.Hom.subschemeProjection X Y I).left := by
  have hI : (I.comap (Hilbert.Functor.ambientMap (X ⨯ Y) a)).subschemeι ≫
      (prod.map a (𝟙 (X ⨯ Y))).left = Hilbert.Functor.familyMap (X ⨯ Y) a I ≫ I.subschemeι :=
    (Hilbert.Functor.family_ambient_isPullback (X ⨯ Y) a I).w
  change ((I.comap (Hilbert.Functor.ambientMap (X ⨯ Y) a)).subschemeι ≫
      (HomFunctor.Hom.graphProjection X Y T).left) ≫ (prod.map a (𝟙 X)).left =
    Hilbert.Functor.familyMap (X ⨯ Y) a I ≫ (I.subschemeι ≫ (HomFunctor.Hom.graphProjection X Y B).left)
  rw [Category.assoc, ← Over.comp_left, HomFunctor.Hom.graphProjection_naturality, Over.comp_left,
    ← Category.assoc, hI,
    Category.assoc]

theorem nativeGraphProjection_baseChange_isIso_iff {T B : Over S} (a : T ⟶ B)
    (I : (Hilbert.Functor.ambient (X ⨯ Y) B).IdealSheafData) :
    IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (GraphLocus.Hom.subschemeProjection X Y I).left
      (Hilbert.Functor.ambientProjection X B) a.left) ↔
      IsIso (GraphLocus.Hom.subschemeProjection X Y (I.comap (Hilbert.Functor.ambientMap (X ⨯ Y) a))) := by
  rw [← isIso_iff_of_reflects_iso
    (GraphLocus.Hom.subschemeProjection X Y (I.comap (Hilbert.Functor.ambientMap (X ⨯ Y) a))) (Over.forget S)]
  apply CartesianMorphismIsomorphismComparison.relativeMorphismBaseChange_isIso_iff_cartesian_comparison
    (GraphLocus.Hom.subschemeProjection X Y I).left (Hilbert.Functor.ambientProjection X B) a.left
    (Hilbert.Functor.familyMap (X ⨯ Y) a I)
    (Hilbert.Functor.familyProjection (X ⨯ Y) (I.comap (Hilbert.Functor.ambientMap (X ⨯ Y) a)))
    (Hilbert.Functor.ambientMap X a) (Hilbert.Functor.ambientProjection X T)
    (GraphLocus.Hom.subschemeProjection X Y (I.comap (Hilbert.Functor.ambientMap (X ⨯ Y) a))).left
  · rw [subschemeProjection_familyProjection]
    exact (Hilbert.Functor.family_isPullback (X ⨯ Y) a I).flip
  · exact (Hilbert.Functor.ambient_isPullback X a).flip
  · exact subschemeProjection_baseChange X Y a I
  · exact subschemeProjection_familyProjection X Y _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphProjectionBaseChange.Hom

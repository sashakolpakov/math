import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionPullbacks
import Mathlib.AlgebraicGeometry.Cover.Directed

/-! # Reference Intersection Directed Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionDirectedCover

noncomputable section

/-! The original intersection cover is directed, so it presents the original scheme as a colimit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

instance originalIntersectionCover_locallyDirected : (ReferenceIntersectionFunctor.originalIntersectionCover X).LocallyDirected where
  trans h := ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).map h).left
  trans_id S := congrArg (fun f => f.left) ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).map_id S)
  trans_comp f g := congrArg (fun h => h.left) ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).map_comp f g)
  w h := X.left.homOfLE_ι (FiniteIntersection.Arrows.finiteIntersectionOpen_antitone X (leOfHom h))
  directed {S T} x := by
    let hS := FiniteIntersection.Unions.finiteIntersection_subset_union_left X S T
    let hT := FiniteIntersection.Unions.finiteIntersection_subset_union_right X S T
    let xi := pullback.fst (Finite.AffineIntersections.finiteIntersectionOpen X S).ι (Finite.AffineIntersections.finiteIntersectionOpen X T).ι x
    let xj := pullback.snd (Finite.AffineIntersections.finiteIntersectionOpen X S).ι (Finite.AffineIntersections.finiteIntersectionOpen X T).ι x
    have hx : (Finite.AffineIntersections.finiteIntersectionOpen X S).ι xi = (Finite.AffineIntersections.finiteIntersectionOpen X T).ι xj :=
      congrArg (fun f => f x) (pullback.condition (f := (Finite.AffineIntersections.finiteIntersectionOpen X S).ι)
        (g := (Finite.AffineIntersections.finiteIntersectionOpen X T).ι))
    obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback (ReferenceIntersectionPullbacks.originalIntersection_pair_isPullback X S T)
      xi xj hx
    refine ⟨FiniteIntersection.Unions.finiteIntersectionUnion X S T, homOfLE hS, homOfLE hT, y, ?_⟩
    apply (pullback.fst (Finite.AffineIntersections.finiteIntersectionOpen X S).ι (Finite.AffineIntersections.finiteIntersectionOpen X T).ι).isOpenEmbedding.injective
    simpa only [← Scheme.Hom.comp_apply, pullback.lift_fst] using hy
  property_trans h := ReferenceIntersectionFunctor.originalIntersectionFunctor_open X h

def originalIntersectionCocone :
    Cocone (ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))) :=
  (ReferenceIntersectionFunctor.originalIntersectionCover X).coconeOfLocallyDirected

def originalIntersection_isColimit : IsColimit (originalIntersectionCocone X) :=
  (ReferenceIntersectionFunctor.originalIntersectionCover X).isColimitCoconeOfLocallyDirected

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionDirectedCover

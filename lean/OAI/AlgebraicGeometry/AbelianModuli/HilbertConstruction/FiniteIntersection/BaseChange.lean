import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Functor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! Base change of the finite intersection functor preserves smooth affine charts and open arrows. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)
variable (D : Subalgebra M.coefficients R)

abbrev IntersectionModel.FiniteIntersectionModel.baseChangedFunctor : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ ⥤ Over (Spec (.of D)) :=
  M.intersectionFunctor ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D)))

abbrev IntersectionModel.FiniteIntersectionModel.baseChangedSchemeFunctor : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ ⥤ Scheme :=
  M.baseChangedFunctor D ⋙ Over.forget _

instance IntersectionModel.FiniteIntersectionModel.baseChangedFunctor_affine (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    IsAffine ((M.baseChangedFunctor D).obj S).left := by
  have : IsAffine (M.chartScheme S) := M.chartOver_affine S
  change IsAffine (pullback (M.chartMap S)
    (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))))
  infer_instance

instance IntersectionModel.FiniteIntersectionModel.baseChangedFunctor_smooth (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    Smooth ((M.baseChangedFunctor D).obj S).hom := by
  have : Smooth (M.chartMap S) := M.chartMap_smooth S
  change Smooth (pullback.snd (M.chartMap S)
    (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))))
  infer_instance

instance IntersectionModel.FiniteIntersectionModel.baseChangedSchemeFunctor_open {S T : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ} (h : S ⟶ T) :
    IsOpenImmersion ((M.baseChangedSchemeFunctor D).map h) :=
  MorphismProperty.of_isPullback
    (Projective.PresentationBaseChange.overPullback_map_isPullback (M.intersectionFunctor.map h)
      (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))))
    (M.intersectionFunctor_open h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

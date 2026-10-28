import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Unions
import Mathlib.CategoryTheory.Category.Preorder

/-! # Reference Intersection Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionFunctor

noncomputable section

/-! The original finite affine intersections form a functor and cover the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

abbrev originalIntersectionFunctor : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ ⥤ Over (Spec (.of R)) where
  obj S := Finite.AffineIntersections.finiteIntersectionChart X S
  map h := FiniteIntersection.Arrows.finiteIntersectionArrow X (leOfHom h)
  map_id S := FiniteIntersection.Arrows.finiteIntersectionArrow_id X S
  map_comp f g := (FiniteIntersection.Arrows.finiteIntersectionArrow_comp X (leOfHom g) (leOfHom f)).symm

instance originalIntersectionFunctor_open {S T : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ} (h : S ⟶ T) :
    IsOpenImmersion ((originalIntersectionFunctor X).map h).left :=
  FiniteIntersection.Arrows.finiteIntersectionArrow_open X (leOfHom h)

abbrev originalIntersectionCover : X.left.OpenCover where
  I₀ := (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ
  X S := (Finite.AffineIntersections.finiteIntersectionChart X S).left
  f S := (Finite.AffineIntersections.finiteIntersectionOpen X S).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro x
    obtain ⟨S, hS⟩ := FiniteIntersection.Unions.finiteIntersectionOpen_cover X x
    exact ⟨S, ⟨x, hS⟩, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionFunctor

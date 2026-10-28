import OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.QuotientComplexPoints

/-!
# Points of an affine quotient

Complex points of `A ⧸ I` are exactly complex-algebra characters of `A` vanishing
on `I`. This is the actual algebraic universal property of the quotient, with
compatibility with the scheme morphism induced by the quotient map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The zero locus of an ideal among actual complex-algebra characters. -/
def affineIdealZeroLocus (I : Ideal A) : Set (AffineComplexPoints.affineComplexPoints A) :=
  {x | ∀ a : A, a ∈ I → x a = 0}

/-- Vanishing on an ideal is equivalently containment of that ideal in the character's kernel. -/
theorem mem_affineIdealZeroLocus_iff_le_ker (I : Ideal A) (x : AffineComplexPoints.affineComplexPoints A) :
    x ∈ affineIdealZeroLocus I ↔ I ≤ RingHom.ker x.toRingHom := Iff.rfl

/-- Complex points of a quotient are exactly characters vanishing on the defining ideal. -/
def quotientComplexPointsEquiv (I : Ideal A) :
    AffineComplexPoints.affineComplexPoints (A ⧸ I) ≃ affineIdealZeroLocus I where
  toFun x := ⟨x.comp (Ideal.Quotient.mkₐ ℂ I), by
    intro a ha
    change x (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]⟩
  invFun x := Ideal.Quotient.liftₐ I x.val x.property
  left_inv x := by
    apply Ideal.Quotient.algHom_ext ℂ
    exact Ideal.Quotient.liftₐ_comp I _ _
  right_inv x := by
    apply Subtype.ext
    exact Ideal.Quotient.liftₐ_comp I _ _

/-- Restricting a quotient point is precomposition by the canonical algebra quotient map. -/
@[simp] theorem quotientComplexPointsEquiv_val (I : Ideal A)
    (x : AffineComplexPoints.affineComplexPoints (A ⧸ I)) :
    (quotientComplexPointsEquiv I x).val = x.comp (Ideal.Quotient.mkₐ ℂ I) := rfl

/-- The inverse is the standard quotient algebra lift. -/
@[simp] theorem quotientComplexPointsEquiv_symm (I : Ideal A)
    (x : affineIdealZeroLocus I) :
    (quotientComplexPointsEquiv I).symm x =
      Ideal.Quotient.liftₐ I x.val x.property := rfl

/-- Quotient points are determined by the resulting characters on the original algebra. -/
theorem quotientComplexPoints_restrict_injective (I : Ideal A) :
    Function.Injective (fun x : AffineComplexPoints.affineComplexPoints (A ⧸ I) =>
      x.comp (Ideal.Quotient.mkₐ ℂ I)) := by
  intro x y h
  apply (quotientComplexPointsEquiv I).injective
  exact Subtype.ext h

/-- The image of restriction is exactly the ideal's zero locus. -/
theorem range_quotientComplexPoints_restrict (I : Ideal A) :
    Set.range (fun x : AffineComplexPoints.affineComplexPoints (A ⧸ I) =>
      x.comp (Ideal.Quotient.mkₐ ℂ I)) = affineIdealZeroLocus I := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (quotientComplexPointsEquiv I y).property
  · intro hx
    refine ⟨(quotientComplexPointsEquiv I).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((quotientComplexPointsEquiv I).apply_symm_apply ⟨x, hx⟩)

/-- On the scheme side, restriction is composition with `Spec` of the quotient map. -/
theorem quotientComplexPointsEquiv_specMap {A : Type} [CommRing A] [Algebra ℂ A]
    (I : Ideal A) (x : AffineComplexPoints.affineComplexPoints (A ⧸ I)) :
    Spec.map (CommRingCat.ofHom (quotientComplexPointsEquiv I x).val.toRingHom) =
      Spec.map (CommRingCat.ofHom x.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [← Spec.map_comp]
  rfl

end OAI.AlgebraicGeometry.Foundations.Scheme.QuotientComplexPoints

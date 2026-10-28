import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteImages

/-! # Positive Scalar -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveScalar

noncomputable section

/-!
# Positive scalar covers on the actual quotient abelian scheme

Finiteness comes from the original finite polarization and the actual Picard
dual, including characteristic-prime multiplication. A finite surjective
quotient transfers finiteness to the target; its smooth group geometry gives
flatness and surjectivity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
  (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Surjective f.left]

include D ell f

omit [IsCommMonObj B] [Smooth B.hom] [GeometricallyConnected B.hom] in
/-- Every positive multiplication map on the actual quotient is finite, in every residue characteristic. -/
theorem quotient_scalar_finite (n : ℕ) (hn : 0 < n) : IsFinite ((𝟙 B) ^ n).left := by
  have : IsFinite ((𝟙 A) ^ n).left := AbelianScheme.CartierDuality.RelativeTorsion.Construction.RelativeAbelian.finite_positive_power A D ell n hn
  have hs : f.left ≫ ((𝟙 B) ^ n).left = ((𝟙 A) ^ n).left ≫ f.left :=
    congrArg Over.Hom.left (by
      rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp] :
      f ≫ (𝟙 B) ^ n = ((𝟙 A) ^ n) ≫ f)
  have : IsFinite (f.left ≫ ((𝟙 B) ^ n).left) := by rw [hs]; infer_instance
  have hp : IsProper (((𝟙 B) ^ n).left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ((𝟙 B) ^ n).left := IsProper.of_comp ((𝟙 B) ^ n).left B.hom
  exact AbelianScheme.CartierDuality.FiniteImages.Construction.Schemes.finite_of_proper_of_surjective_comp f.left ((𝟙 B) ^ n).left

/-- Positive scalar multiplication on the quotient is an effective epimorphism by actual geometric theorems. -/
theorem quotient_scalar_effective (n : ℕ) (hn : 0 < n) : EffectiveEpi ((𝟙 B) ^ n) := by
  have : IsFinite ((𝟙 B) ^ n).left := quotient_scalar_finite D ell f n hn
  exact AbelianScheme.CartierDuality.MultiplicationCovers.Construction.Multiplication.effectiveEpi_power_of_isFinite B n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveScalar

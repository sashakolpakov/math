import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers

/-! # Positive Multiple -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveMultiple

/-! A positive integer multiple of the original finite flat polarization is an actual isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
  (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]

theorem positive_multiple_cover (n : ℕ) (hn : 0 < n) :
    IsFinite (ell ^ n).left ∧ Flat (ell ^ n).left ∧ Surjective (ell ^ n).left := by
  obtain ⟨hf, hflat, hs, _⟩ := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  have hh : ((𝟙 A) ^ n).left ≫ ell.left = (ell ^ n).left :=
    congrArg Over.Hom.left (by rw [MonObj.pow_comp, Category.id_comp] : ((𝟙 A) ^ n) ≫ ell = ell ^ n)
  have hf' : IsFinite (((𝟙 A) ^ n).left ≫ ell.left) := inferInstance
  have hflat' : Flat (((𝟙 A) ^ n).left ≫ ell.left) := inferInstance
  have hs' : Surjective (((𝟙 A) ^ n).left ≫ ell.left) := inferInstance
  rw [hh] at hf' hflat' hs'
  exact ⟨hf', hflat', hs'⟩

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveMultiple

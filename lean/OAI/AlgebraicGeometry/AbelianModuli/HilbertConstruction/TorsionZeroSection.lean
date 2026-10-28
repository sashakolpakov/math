import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedSections

/-! # Torsion Zero Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The zero section of full-level torsion is an open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.torsionZeroSection (n : ℕ) : 𝟙_ (Over S) ⟶ A.torsionScheme n :=
  (A.torsionSchemePointsEquiv n _).symm ⟨1, one_pow n⟩

@[reassoc (attr := simp)] theorem Abelian.Schemes.AbelianScheme.torsionZeroSection_inclusion (n : ℕ) :
    A.torsionZeroSection n ≫ A.torsionInclusion n = 1 :=
  congrArg (fun x : A.torsionPoints n (𝟙_ (Over S)) => x.val)
    ((A.torsionSchemePointsEquiv n _).apply_symm_apply ⟨1, one_pow n⟩)

theorem Abelian.Schemes.AbelianScheme.torsionZeroSection_isOpenImmersion {n : ℕ} (level : A.FullLevel n) :
    IsOpenImmersion (A.torsionZeroSection n).left := by
  have := level.torsion_etale
  exact UnramifiedSections.section_isOpenImmersion_of_unramified (A.torsionScheme n).hom
    (A.torsionZeroSection n).left (A.torsionZeroSection n).w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

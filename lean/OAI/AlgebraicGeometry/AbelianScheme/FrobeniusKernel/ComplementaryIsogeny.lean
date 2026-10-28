import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveScalar
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.Complement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupHomFlat

/-! # Complementary Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ComplementaryIsogeny.Construction

noncomputable section

/-! Construct a complementary isogeny to a quotient using the original
dual and positive scalar geometry. No dual for the quotient is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ}
variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A DA.abelian)
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
variable (hkernel : ∀ (T : Over S) (x : T ⟶ A.scheme),
  x ≫ f.hom = 1 → x ^ n = 1)

include ell hn hkernel in
theorem exists_complementary_isogeny :
    ∃ d : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A,
      f.hom ≫ d.hom = (𝟙 A.scheme) ^ n ∧
      d.hom ≫ f.hom = (𝟙 B.scheme) ^ n := by
  obtain ⟨d, hd, hfd, hdf⟩ := Power.Construction.exists_complementary_isogeny_map f n hkernel
  have : IsMonHom d := hd
  have : IsMonHom (show A.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from ell.hom) :=
    ell.preservesGroup
  have : IsFinite (show A.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from ell.hom).left :=
    ell.finite
  have : IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left :=
    CartierDuality.RelativeTorsion.Construction.RelativeAbelian.finite_positive_power A.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) ell.hom n hn
  have : Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left :=
    CartierDuality.MultiplicationCovers.Construction.Multiplication.surjective_power_of_isFinite A.scheme n
  have : IsFinite ((𝟙 B.scheme : B.scheme ⟶ B.scheme) ^ n).left :=
    Picard.PoincareBundle.PositiveScalar.quotient_scalar_finite (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) ell.hom f.hom n hn
  have hfinite : IsFinite d.left :=
    Picard.PoincareBundle.Scalar.Complement.finite_of_scalar_complement d f.hom n hdf
  have hsurjective : Surjective d.left :=
    Picard.PoincareBundle.Scalar.Complement.surjective_of_scalar_complement d f.hom n hfd
  have hflat : Flat d.left := IsogenyQuotient.Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat d
  exact ⟨⟨d, hd, hfinite, hflat, hsurjective⟩, hfd, hdf⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ComplementaryIsogeny.Construction

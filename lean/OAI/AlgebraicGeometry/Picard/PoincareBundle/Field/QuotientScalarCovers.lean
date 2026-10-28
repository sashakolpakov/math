import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveScalar
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies

/-! # Quotient Scalar Covers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.QuotientScalarCovers

/-! The original finite polarization supplies effective scalar quotients on its isogenous target over any field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard

variable {k : Type u} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

include D ell f

/-- Positive multiplication on the actual quotient is an effective epimorphism, with no characteristic hypothesis. -/
theorem effective (n : ℕ) (hn : 0 < n) : EffectiveEpi ((𝟙 B.scheme) ^ n) := by
  have : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from ell.hom) := ell.preservesGroup
  have : IsFinite (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from ell.hom).left := ell.finite
  exact PositiveScalar.quotient_scalar_effective (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) ell.hom f.hom n hn

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.QuotientScalarCovers

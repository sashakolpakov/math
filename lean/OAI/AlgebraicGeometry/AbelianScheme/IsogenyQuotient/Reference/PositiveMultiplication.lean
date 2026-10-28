import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

/-! # Positive Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PositiveMultiplication.Construction

noncomputable section

/-! The original finite polarization supplies all geometric properties
of positive multiplication used by the parameter-character construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard

universe u

theorem originalPositiveMultiplication_properties {S : Scheme.{u}} {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ}
    (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 A.scheme) ^ n).left ∧ Flat ((𝟙 A.scheme) ^ n).left ∧
      Surjective ((𝟙 A.scheme) ^ n).left ∧ LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := by
  have : IsMonHom (show A.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from pol.isogeny.hom) :=
    pol.isogeny.preservesGroup
  have : IsFinite (show A.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from pol.isogeny.hom).left :=
    pol.isogeny.finite
  exact CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) pol.isogeny.hom n hn

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PositiveMultiplication.Construction

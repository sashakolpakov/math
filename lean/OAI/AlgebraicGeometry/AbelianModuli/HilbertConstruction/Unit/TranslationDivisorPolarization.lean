import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.TranslationDivisorPolarization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DivisorPolarization

/-! # Translation Divisor Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Recover the original polarization from the translation quotient and
the raw graph comparison when twice the graph exponent is invertible.
These constructors retain arbitrary, possibly nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- The actual translation quotient and raw graph comparison give the
original polarization when the dividing integer is invertible. -/
def PolarizationData.Polarization.ofAmpleUnitTranslationDivisor
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (recover : (D.poincare.pullback (m ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf)
    (hp : A.multiplication (2 * d) ≫ p.hom = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p.hom).tensorPower d).sheaf) : PolarizationData.Polarization D δ :=
  PolarizationData.Polarization.ofAmpleNormalizedUnitDivisorGraphPower D p δ hδ d hd hunit m L hL
    (Rational.TranslationDivisorPolarization.translationDifferenceNormalizedInducingFormula D m L recover) hp eG

/-- This form matches the raw graph-power parameter over any test
scheme, with ampleness required only for the original affine-base line. -/
def PolarizationData.Polarization.ofBaseChangedAmpleUnitTranslationDivisor
    {S T : Scheme} [IsAffine S] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (b : T ⟶ S)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback b) (D.abelian.pullback b))
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (recover : (D.poincare.pullback (m ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf)
    (hp : (A.pullback b).multiplication (2 * d) ≫ p.hom = (Over.pullback b).map m)
    (eG : ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom b)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback b) p.hom).tensorPower d).sheaf) :
    PolarizationData.Polarization (D.pullback b) δ :=
  PolarizationData.Polarization.ofBaseChangedNormalizedUnitDivisorGraphPower D b p δ hδ d hd hunit m L hL
    (Rational.TranslationDivisorPolarization.translationDifferenceNormalizedInducingFormula D m L recover) hp eG

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

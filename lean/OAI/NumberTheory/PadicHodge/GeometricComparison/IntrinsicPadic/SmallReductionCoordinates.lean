import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FirstThreeCrystalline
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReductionCoordinates

/-! # Small Reduction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates

noncomputable section

/-! Original native de Rham reduction in the small ordinary
quotient Cech coordinates used by the finite comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] (n : ℕ)

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "I" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)

def map : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 →ₗ[ℤ_[p]] (Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology 1 :=
  (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv.hom.comp
    (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n + 1))

theorem homology_coordinates : (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv ≫
    (Coefficient.IntrinsicPadicSmallQuotientTotal.firstThreeHomologyIso p X n).hom =
      (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U I 1).hom := by
  let a := Coefficient.IntrinsicPadicSmallQuotientTotal.firstThreeHomologyIso p X n
  let b := IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U I 1
  exact (Category.assoc b.hom a.inv a.hom).trans
    ((congrArg (fun c => b.hom ≫ c) a.inv_hom_id).trans (Category.comp_id b.hom))

theorem coordinates (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    (Coefficient.IntrinsicPadicSmallQuotientTotal.firstThreeHomologyIso p X n).hom (map p X n x) =
      (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U I 1).hom
        (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n + 1) x) :=
  ConcreteCategory.congr_hom (homology_coordinates p X n)
    (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n + 1) x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates

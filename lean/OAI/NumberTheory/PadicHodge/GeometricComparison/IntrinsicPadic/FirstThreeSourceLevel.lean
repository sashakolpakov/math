import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FirstThreeCrystalline
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallQuotientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.AffineQuotientCechLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientTransitionCoordinates

/-! # First Three Source Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FirstThreeSourceLevel.IntrinsicPadicFirstThreeSourceLevel

noncomputable section

/-! The actual small p-adic quotient Cech H-one identifies naturally
with the original principal quotient tower used by integral completion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem three_squares {A : Type*} [Category* A] {W X Y Z W' X' Y' Z' : A}
    (p : W ⟶ W') (q : X ⟶ X') (r : Y ⟶ Y') (s : Z ⟶ Z')
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (a' : W' ⟶ X') (b' : X' ⟶ Y') (c' : Y' ⟶ Z')
    (h₁ : p ≫ a' = a ≫ q) (h₂ : q ≫ b' = b ≫ r) (h₃ : r ≫ c' = c ≫ s) :
    p ≫ (a' ≫ b' ≫ c') = (a ≫ b ≫ c) ≫ s := by
  have h := ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂
  have h' := ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h h₃
  simpa only [Category.assoc] using h'

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n m : ℕ) (hnm : n ≤ m)

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U
local notation "Im" => (Ideal.span {(p : ℤ_[p])}) ^ (m + 1)
local notation "In" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)
local notation "hI" => Ideal.pow_le_pow_right (I := Ideal.span {(p : ℤ_[p])}) (Nat.add_le_add_right hnm 1)

def principalMap : PrincipalCochainExact.PrincipalCochainQuotient.quotient ℤ_[p] C (p : ℤ_[p]) (m + 1) ⟶
    PrincipalCochainExact.PrincipalCochainQuotient.quotient ℤ_[p] C (p : ℤ_[p]) (n + 1) :=
  PrincipalCochainExact.PrincipalCochainQuotient.transition ℤ_[p] C (p : ℤ_[p]) (n + 1) (m + 1) (Nat.add_le_add_right hnm 1)

theorem full_open : SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm ≫ (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).hom =
    (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X m).hom ≫ IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel.map ℤ_[p] X U Im In hI :=
  AffineQuotientCechLevel.OrdinaryAffineQuotientCechLevel.natural ℤ_[p] X (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X) Im In hI

theorem full_open_homology : HomologicalComplex.homologyMap (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) 1 ≫
    HomologicalComplex.homologyMap (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).hom 1 =
    HomologicalComplex.homologyMap (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X m).hom 1 ≫
      HomologicalComplex.homologyMap (IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel.map ℤ_[p] X U Im In hI) 1 :=
  (HomologicalComplex.homologyMap_comp (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm)
    (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).hom 1).symm.trans
      ((congrArg (fun q => HomologicalComplex.homologyMap q 1) (full_open p X n m hnm)).trans
        (HomologicalComplex.homologyMap_comp (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X m).hom
          (IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel.map ℤ_[p] X U Im In hI) 1))

omit [X.left.IsSeparated] in
theorem principal : principalMap p X n m hnm ≫ (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U In).hom =
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U Im).hom ≫ IntegralCech.QuotientLevel.IntegralCechQuotientLevel.map ℤ_[p] X U Im In hI :=
  (congrArg (fun q => q ≫ (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U In).hom)
    (CochainQuotientTransitionCoordinates.PrincipalCochainQuotientTransitionCoordinates.transition ℤ_[p] C (p : ℤ_[p])
      (n + 1) (m + 1) (Nat.add_le_add_right hnm 1))).trans
        (IntegralCech.QuotientLevel.IntegralCechQuotientLevel.natural ℤ_[p] X U Im In hI)

omit [X.left.IsSeparated] in
theorem inverse_principal : IntegralCech.QuotientLevel.IntegralCechQuotientLevel.map ℤ_[p] X U Im In hI ≫
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U In).inv =
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U Im).inv ≫ principalMap p X n m hnm :=
  IntegralComparison.InverseCoordinateHomology.inverse (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U Im)
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U In) (principalMap p X n m hnm)
    (IntegralCech.QuotientLevel.IntegralCechQuotientLevel.map ℤ_[p] X U Im In hI) (principal p X n m hnm)

omit [X.left.IsSeparated] in
theorem inverse_principal_homology : HomologicalComplex.homologyMap (IntegralCech.QuotientLevel.IntegralCechQuotientLevel.map ℤ_[p] X U Im In hI) 1 ≫
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U In 1).inv =
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U Im 1).inv ≫ HomologicalComplex.homologyMap (principalMap p X n m hnm) 1 :=
  (HomologicalComplex.homologyMap_comp (IntegralCech.QuotientLevel.IntegralCechQuotientLevel.map ℤ_[p] X U Im In hI)
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U In).inv 1).symm.trans
      ((congrArg (fun q => HomologicalComplex.homologyMap q 1) (inverse_principal p X n m hnm)).trans
        (HomologicalComplex.homologyMap_comp (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U Im).inv (principalMap p X n m hnm) 1))

theorem natural : HomologicalComplex.homologyMap (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) 1 ≫
    (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).hom =
    (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X m).hom ≫ HomologicalComplex.homologyMap (principalMap p X n m hnm) 1 :=
  three_squares _ _ _ _ _ _ _ _ _ _ (full_open_homology p X n m hnm)
    (IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel.homology ℤ_[p] X U Im In hI) (inverse_principal_homology p X n m hnm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FirstThreeSourceLevel.IntrinsicPadicFirstThreeSourceLevel

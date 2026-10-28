import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IdealClosedFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.HomogeneousCoordinates

/-! # Closed Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The equivalence between saturated flat Hilbert ideals and actual flat closed Hilbert families in projective space. -/

open _root_.AlgebraicGeometry

universe u

def Flat.ClosedFamilies.FlatClosedHilbertFamily (R : Type u) [CommRing R] (n : ℕ) (P : Polynomial ℚ) :=
  {F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n) // ∀ p : PrimeSpectrum R,
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) F.homogeneousIdeal)).toIdeal P}

variable {R : Type u} [CommRing R] {n : ℕ} {P : Polynomial ℚ}

def Flat.ClosedFamilies.FlatClosedHilbertFamily.saturatedIdeal (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) :
    SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P where
  ideal := F.val.homogeneousIdeal
  saturated := F.val.homogeneousIdeal_saturated
  flat := F.val.homogeneousIdeal_flat
  hilbert := F.property

variable [IsNoetherianRing R]

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.closedFamily_homogeneousIdeal (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P) :
    I.closedFamily.homogeneousIdeal = I.ideal :=
  HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_projectiveQuotient I.ideal I.saturated

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.closedHilbertFamily (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P) :
    Flat.ClosedFamilies.FlatClosedHilbertFamily R n P := ⟨I.closedFamily, by
  rw [I.closedFamily_homogeneousIdeal]
  exact I.hilbert⟩

def Flat.ClosedFamilies.saturatedFlatHilbertClosedFamilyEquiv : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P ≃ Flat.ClosedFamilies.FlatClosedHilbertFamily R n P where
  toFun := SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.closedHilbertFamily
  invFun := Flat.ClosedFamilies.FlatClosedHilbertFamily.saturatedIdeal
  left_inv I := SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.ext I.closedFamily_homogeneousIdeal
  right_inv F := by
    apply Subtype.ext
    apply Closed.Families.FlatClosedFamily.ext
    exact HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf F.val.ideal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

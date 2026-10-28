import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Coordinate
import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalImage

/-! # Integral Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCoordinates.IntrinsicPadicIntegralHodgeCoordinates

noncomputable section

/-! Every native integral Hodge class has a representative in the
form-degree truncation of the actual etale-cover Cech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex₂

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex ℤ_[p] X U

theorem exists_representative (r : ℤ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1)
    (hx : x ∈ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[p] X 1 r) :
    ∃ a : (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r) (.up ℕ)).homology 1,
      NaturalTotalImage.NaturalTotalHodgeImage.filtrationMap B 1 r a = IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X x := by
  have hx' : x ∈ (FlatFiltered.FlatFilteredTotalCohomology.filtration B (1 : ℤ) r).map
      (IntegralCech.Coordinate.IntegralCechCoordinateHodge.equiv ℤ_[p] X U
        (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X)
        (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X)).toLinearMap := by
    rw [IntegralCech.Coordinate.IntegralCechCoordinateHodge.equiv_filtration]
    exact hx
  rcases hx' with ⟨_, ⟨a, rfl⟩, ha⟩
  refine ⟨((HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r) (.up ℕ)).extendHomologyIso
    ComplexShape.embeddingUpNat (j := 1) rfl).hom a, ?_⟩
  rw [← ha]
  change _ = (((B).total (.up ℕ)).extendHomologyIso
    ComplexShape.embeddingUpNat (j := 1) rfl).toLinearEquiv
      ((IntegralCech.Coordinate.IntegralCechCoordinateHodge.equiv ℤ_[p] X U
        (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X)
        (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X)).symm
          ((IntegralCech.Coordinate.IntegralCechCoordinateHodge.equiv ℤ_[p] X U
            (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X)
            (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X))
              (FlatFiltered.FlatFilteredTotalCohomology.filtrationMap B (1 : ℤ) r a)))
  exact (NaturalTotalImage.NaturalTotalHodgeImage.extend_filtrationMap B 1 r a).symm.trans
    (congrArg (((B).total (.up ℕ)).extendHomologyIso
      ComplexShape.embeddingUpNat (j := 1) rfl).toLinearEquiv
        ((IntegralCech.Coordinate.IntegralCechCoordinateHodge.equiv ℤ_[p] X U
          (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X)
          (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X)).symm_apply_apply
            (FlatFiltered.FlatFilteredTotalCohomology.filtrationMap B (1 : ℤ) r a)).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCoordinates.IntrinsicPadicIntegralHodgeCoordinates

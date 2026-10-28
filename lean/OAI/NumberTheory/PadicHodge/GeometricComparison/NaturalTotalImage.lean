import OAI.NumberTheory.PadicHodge.GeometricComparison.FlatFiltered
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Natural Total Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalImage.NaturalTotalHodgeImage

noncomputable section

/-! Extending a nonnegative Cech total to integer degrees preserves
the actual form-degree Hodge image on cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {R : Type} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ)) (n : ℕ) (r : ℤ)

def filtrationMap : (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) (.up ℕ)).homology n →ₗ[R]
    (K.total (.up ℕ)).homology n :=
  (HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)) n).hom

def filtration : Submodule R ((K.total (.up ℕ)).homology n) :=
  LinearMap.range (filtrationMap K n r)

theorem extend_filtrationMap
    (a : ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).homology (n : ℤ)) :
    ((K.total (.up ℕ)).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom
      (FlatFiltered.FlatFilteredTotalCohomology.filtrationMap K (n : ℤ) r a) =
    filtrationMap K n r
      (((HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) (.up ℕ)).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).hom a) :=
  ConcreteCategory.congr_hom (HomologicalComplex.extendHomologyIso_hom_naturality
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ))
    ComplexShape.embeddingUpNat (j := n) rfl) a

theorem extend_filtration :
    (FlatFiltered.FlatFilteredTotalCohomology.filtration K (n : ℤ) r).map
      ((K.total (.up ℕ)).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom.hom =
        filtration K n r := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨((HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) (.up ℕ)).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) rfl).hom a, (extend_filtrationMap K n r a).symm⟩
  · rintro ⟨a, rfl⟩
    let e := (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) (.up ℕ)).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) rfl
    refine ⟨FlatFiltered.FlatFilteredTotalCohomology.filtrationMap K (n : ℤ) r (e.inv a), ⟨e.inv a, rfl⟩, ?_⟩
    exact (extend_filtrationMap K n r (e.inv a)).trans
      (congrArg (filtrationMap K n r) (e.toLinearEquiv.apply_symm_apply a))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalImage.NaturalTotalHodgeImage

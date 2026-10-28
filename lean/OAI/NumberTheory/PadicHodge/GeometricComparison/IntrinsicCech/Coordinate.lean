import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionTotalNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineCechCoordinateUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TruncatedSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlatFiltered
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarTotal

/-! # Coordinate -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Coordinate.IntrinsicCechCoordinateHodge

noncomputable section

/-! The form-degree filtration on the actual coordinate Čech total is exactly the original native Hodge filtration. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

def bicomplexIso : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U ≅
    SectionsTotal.IntrinsicCechSectionsTotal.bicomplex R X.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
  Intrinsic.AffineCechCoordinateUnit.IntrinsicAffineCechCoordinateUnit.iso R X U hU ≪≫
    (CechBicomplex.IntrinsicCechBicomplex.sectionIso R X U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).symm

def totalIso : ScalarTotal.IntrinsicCechScalarTotal.complex R X U ≅ TruncatedSections.IntrinsicCechHodgeComparison.sections R X U :=
  (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).mapIso (bicomplexIso R X U hU) ≪≫
    SectionsTotal.IntrinsicCechSectionsTotal.iso R X.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)

def truncatedIso (r : ℤ) :
    (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) r) ≅
      TruncatedSections.IntrinsicCechHodgeComparison.truncatedSections R X U r :=
  (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).mapIso
    (TruncatedFunctorIso.TruncatedPullback.iso (SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left U) (bicomplexIso R X U hU).symm r).symm ≪≫
      SectionsTotal.IntrinsicCechSectionsTotal.iso R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)

omit [Finite ι] in
theorem inclusion_square (r : ℤ) :
    (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) r) ≫ (totalIso R X U hU).hom =
      (truncatedIso R X U hU r).hom ≫ SectionTotalNaturality.IntrinsicCechSectionTotalNaturality.sectionMap R X U
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r) := by
  have h₁ := congrArg (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map
    (TruncatedFunctorIso.TruncatedPullback.iso_inv_inclusion (SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left U)
      (bicomplexIso R X U hU).symm r).symm
  simp only [Functor.map_comp] at h₁
  have h₂ := SectionTotalNaturality.IntrinsicCechSectionTotalNaturality.naturality R X U
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

variable (hcover : iSup U = ⊤)

def equiv (n : ℕ) : (ScalarTotal.IntrinsicCechScalarTotal.complex R X U).homology (n : ℤ) ≃ₗ[R]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) (n : ℤ)).mapIso
    (totalIso R X U hU)).toLinearEquiv.trans (TruncatedSections.IntrinsicCechHodgeComparison.equiv R X U hU hcover n)

def truncatedEquiv (n : ℕ) (r : ℤ) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) (n : ℤ)).mapIso
    (truncatedIso R X U hU r)).toLinearEquiv.trans
      (TruncatedSections.IntrinsicCechHodgeComparison.truncatedEquiv R X U hU hcover r n)

theorem equiv_filtrationMap (n : ℕ) (r : ℤ)
    (a : ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) r)).homology (n : ℤ)) :
    equiv R X U hU hcover n (FlatFiltered.FlatFilteredTotalCohomology.filtrationMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) (n : ℤ) r a) =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtrationMap R X n r (truncatedEquiv R X U hU hcover n r a) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) (n : ℤ)
  have hs := (H.map_comp
    ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) r)) (totalIso R X U hU).hom).symm.trans
    ((congrArg H.map (inclusion_square R X U hU r)).trans
      (H.map_comp (truncatedIso R X U hU r).hom
        (SectionTotalNaturality.IntrinsicCechSectionTotalNaturality.sectionMap R X U
          (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r))))
  have ha := ConcreteCategory.congr_hom hs a
  exact (congrArg (TruncatedSections.IntrinsicCechHodgeComparison.equiv R X U hU hcover n) ha).trans
    (TruncatedSections.IntrinsicCechHodgeComparison.equiv_filtrationMap R X U hU hcover n r _)

theorem equiv_filtration (n : ℕ) (r : ℤ) :
    (FlatFiltered.FlatFilteredTotalCohomology.filtration (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) (n : ℤ) r).map
      (equiv R X U hU hcover n).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨truncatedEquiv R X U hU hcover n r a, (equiv_filtrationMap R X U hU hcover n r a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := (truncatedEquiv R X U hU hcover n r).surjective a
    exact ⟨FlatFiltered.FlatFilteredTotalCohomology.filtrationMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) (n : ℤ) r b,
      ⟨b, rfl⟩, equiv_filtrationMap R X U hU hcover n r b⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Coordinate.IntrinsicCechCoordinateHodge

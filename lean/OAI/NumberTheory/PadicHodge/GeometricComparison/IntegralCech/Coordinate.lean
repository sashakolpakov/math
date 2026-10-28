import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionTotalNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Sections
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlatFiltered
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalOneBaseChange

/-! # Coordinate -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Coordinate.IntegralCechCoordinateHodge

noncomputable section

/-! The form-degree filtration on the actual coordinate Čech total is exactly the original native Hodge filtration. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

def bicomplexIso : IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U ≅
    IntrinsicCech.SectionsTotal.IntrinsicCechSectionsTotal.bicomplex R X.left U (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) :=
  IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.iso R X U hU ≪≫
    (IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.sectionIso R X U (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))).symm

abbrev totalIso := IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.totalIso R X U hU

omit [Finite ι] [Module.Flat ℤ R] in
theorem totalIso_hom : (totalIso R X U hU).hom =
    (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map (bicomplexIso R X U hU).hom ≫
      (IntrinsicCech.SectionsTotal.IntrinsicCechSectionsTotal.iso R X.left U
        (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))).hom := by
  change _ = (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map
    ((IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.iso R X U hU).hom ≫
      (IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.sectionIso R X U
        (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))).inv) ≫ _
  erw [Functor.map_comp, Category.assoc]
  rfl

def truncatedIso (r : ℤ) :
    (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U) r) ≅
      Sections.IntegralCechHodgeComparison.truncatedSections R X U r :=
  (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).mapIso
    (TruncatedFunctorIso.TruncatedPullback.iso (IntrinsicCech.SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left U) (bicomplexIso R X U hU).symm r).symm ≪≫
      IntrinsicCech.SectionsTotal.IntrinsicCechSectionsTotal.iso R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) r)

omit [Finite ι] [Module.Flat ℤ R] in
theorem inclusion_square (r : ℤ) :
    (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U) r) ≫ (totalIso R X U hU).hom =
      (truncatedIso R X U hU r).hom ≫ IntrinsicCech.SectionTotalNaturality.IntrinsicCechSectionTotalNaturality.sectionMap R X U
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) r) := by
  have h₁ := congrArg (TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map
    (TruncatedFunctorIso.TruncatedPullback.iso_inv_inclusion (IntrinsicCech.SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left U)
      (bicomplexIso R X U hU).symm r).symm
  simp only [Functor.map_comp] at h₁
  have h₂ := IntrinsicCech.SectionTotalNaturality.IntrinsicCechSectionTotalNaturality.naturality R X U
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) r)
  rw [totalIso_hom]
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

variable (hcover : iSup U = ⊤)

abbrev equiv := Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv R X U hU hcover

def truncatedEquiv (r : ℤ) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) (1 : ℤ)).mapIso
    (truncatedIso R X U hU r)).toLinearEquiv.trans
      (Sections.IntegralCechHodgeComparison.truncatedEquiv R X U hU hcover r)

theorem equiv_filtrationMap (r : ℤ)
    (a : ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U) r)).homology (1 : ℤ)) :
    equiv R X U hU hcover (FlatFiltered.FlatFilteredTotalCohomology.filtrationMap (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U) (1 : ℤ) r a) =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtrationMap R X 1 r (truncatedEquiv R X U hU hcover r a) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) (1 : ℤ)
  have hs := (H.map_comp
    ((TotalFinite.IntegerTotalFunctor.functor (ModuleCat.{0} R)).map
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U) r)) (totalIso R X U hU).hom).symm.trans
    ((congrArg H.map (inclusion_square R X U hU r)).trans
      (H.map_comp (truncatedIso R X U hU r).hom
        (IntrinsicCech.SectionTotalNaturality.IntrinsicCechSectionTotalNaturality.sectionMap R X U
          (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) r))))
  have ha := ConcreteCategory.congr_hom hs a
  exact (congrArg (Sections.IntegralCechHodgeComparison.equiv R X U hU hcover) ha).trans
    (Sections.IntegralCechHodgeComparison.equiv_filtrationMap R X U hU hcover r _)

theorem equiv_filtration (r : ℤ) :
    (FlatFiltered.FlatFilteredTotalCohomology.filtration (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U) (1 : ℤ) r).map
      (equiv R X U hU hcover).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X 1 r := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨truncatedEquiv R X U hU hcover r a, (equiv_filtrationMap R X U hU hcover r a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := (truncatedEquiv R X U hU hcover r).surjective a
    exact ⟨FlatFiltered.FlatFilteredTotalCohomology.filtrationMap (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U) (1 : ℤ) r b,
      ⟨b, rfl⟩, equiv_filtrationMap R X U hU hcover r b⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Coordinate.IntegralCechCoordinateHodge

import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DerivedComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality

/-! # Derived Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DerivedNaturality

noncomputable section

/-! The supported derived comparison preserves the actual maps, via genuine supported cochain homotopies. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O U : Opens X)
variable {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (f : K ⟶ L)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (heK : ∀ n, K.ExactAt (n+1))
variable (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (heL : ∀ n, L.ExactAt (n+1))

theorem flasqueSupportedDerivedCohomologyIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SectionQuasiIso.supportedSheafComplexMap O f)) n ≫
        (DerivedComparison.flasqueSupportedDerivedCohomologyIso O U L hL heL n).hom =
      (DerivedComparison.flasqueSupportedDerivedCohomologyIso O U K hK heK n).hom ≫
        ((DerivedComparison.supportedSectionsFunctor O U).rightDerived n).map (HomologicalComplex.homologyMap f 0) := by
  let I := HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)
  let J := HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (L.homology 0)
  let F := DerivedComparison.supportedSectionsFunctor O U
  let F' := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let G := (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)
  let d := InjectiveResolution.desc (HomologicalComplex.homologyMap f 0) J I
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n
  have hh : H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O f)) ≫
      H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift L heL J))) =
    H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K heK I))) ≫
      H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O d)) := by
    change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
      HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp,
      ← SectionQuasiIso.supportedSheafComplexMap_comp, ← SectionQuasiIso.supportedSheafComplexMap_comp]
    exact ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomotopy
      (ClosedSupportFunctor.supportedSheafComplexMapHomotopy O (HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality.Constructions.resolutionLiftNaturalityHomotopy f heK heL I J))).homologyMap_eq n
  have hd : H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O d)) ≫
      H.map (DerivedComparison.supportedSectionsFunctorIso O U J.cocomplex).hom =
    H.map (DerivedComparison.supportedSectionsFunctorIso O U I.cocomplex).hom ≫ H.map (F'.map d) := by
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (DerivedComparison.supportedSectionsFunctorIso_naturality O U d)
  have hn := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (HomologicalComplex.homologyMap f 0) I J d
    (InjectiveResolution.desc_commutes_zero (HomologicalComplex.homologyMap f 0) J I) F n
  change (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map (HomologicalComplex.homologyMap f 0) =
    H.map (F'.map d) ≫ (J.isoRightDerivedObj F n).inv at hn
  change H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O f)) ≫
      (H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift L heL J))) ≫
        H.map (DerivedComparison.supportedSectionsFunctorIso O U J.cocomplex).hom ≫ (J.isoRightDerivedObj F n).inv) =
    (H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K heK I))) ≫
      H.map (DerivedComparison.supportedSectionsFunctorIso O U I.cocomplex).hom ≫ (I.isoRightDerivedObj F n).inv) ≫
        (F.rightDerived n).map (HomologicalComplex.homologyMap f 0)
  rw [← Category.assoc (H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O f))), hh]
  simp only [Category.assoc]
  rw [← Category.assoc (H.map (G.map (SectionQuasiIso.supportedSheafComplexMap O d))), hd]
  simp only [Category.assoc]
  rw [← hn]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DerivedNaturality

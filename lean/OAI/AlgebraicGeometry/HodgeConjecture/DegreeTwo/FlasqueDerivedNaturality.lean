import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ResolutionHomotopy

/-! # Flasque Derived Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality.Constructions

noncomputable section

/-! The all-degree flasque-to-derived comparison intertwines every actual cochain map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

section LiftNaturality

variable {C : Type*} [Category C] [Abelian C]
variable {K L : CochainComplex C ℕ} (f : K ⟶ L)
variable (hK : ∀ n, K.ExactAt (n+1)) (hL : ∀ n, L.ExactAt (n+1))
variable (I : InjectiveResolution (K.homology 0)) (J : InjectiveResolution (L.homology 0))

def resolutionLiftNaturalityHomotopy :
    Homotopy (f ≫ ResolutionHomotopy.Constructions.resolutionLift L hL J)
      (ResolutionHomotopy.Constructions.resolutionLift K hK I ≫ InjectiveResolution.desc (HomologicalComplex.homologyMap f 0) J I) := by
  apply ResolutionHomotopy.Constructions.resolutionHomotopy K J.cocomplex hK
  rw [← Category.assoc, ← ThomResolutionDiagram.Constructions.cochainZeroHomologyAugmentation_naturality f, Category.assoc,
    ResolutionHomotopy.Constructions.resolutionLift_augmentation, ← Category.assoc, ResolutionHomotopy.Constructions.resolutionLift_augmentation,
    InjectiveResolution.desc_commutes]

end LiftNaturality

variable {X : TopCat.{0}}
variable {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (f : K ⟶ L)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (heK : ∀ n, K.ExactAt (n+1))
variable (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (heL : ∀ n, L.ExactAt (n+1))

theorem flasqueResolutionDerivedCohomologyIso_naturality (U : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
        (FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso L hL heL U n).hom =
      (FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso K hK heK U n).hom ≫
        ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).rightDerived n).map (HomologicalComplex.homologyMap f 0) := by
  let I := FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)
  let J := FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (L.homology 0)
  let F := CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U
  let F' := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let d := InjectiveResolution.desc (HomologicalComplex.homologyMap f 0) J I
  have hh : HomologicalComplex.homologyMap (F'.map f) n ≫
      HomologicalComplex.homologyMap (F'.map (ResolutionHomotopy.Constructions.resolutionLift L heL J)) n =
    HomologicalComplex.homologyMap (F'.map (ResolutionHomotopy.Constructions.resolutionLift K heK I)) n ≫
      HomologicalComplex.homologyMap (F'.map d) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp]
    exact (F.mapHomotopy (resolutionLiftNaturalityHomotopy f heK heL I J)).homologyMap_eq n
  have hn := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (HomologicalComplex.homologyMap f 0) I J d
    (InjectiveResolution.desc_commutes_zero (HomologicalComplex.homologyMap f 0) J I) F n
  change (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map (HomologicalComplex.homologyMap f 0) =
    HomologicalComplex.homologyMap (F'.map d) n ≫ (J.isoRightDerivedObj F n).inv at hn
  change HomologicalComplex.homologyMap (F'.map f) n ≫
      (HomologicalComplex.homologyMap (F'.map (ResolutionHomotopy.Constructions.resolutionLift L heL J)) n ≫
        (J.isoRightDerivedObj F n).inv) =
    (HomologicalComplex.homologyMap (F'.map (ResolutionHomotopy.Constructions.resolutionLift K heK I)) n ≫
      (I.isoRightDerivedObj F n).inv) ≫ (F.rightDerived n).map (HomologicalComplex.homologyMap f 0)
  rw [← Category.assoc, hh, Category.assoc, ← hn, ← Category.assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedNaturality.Constructions

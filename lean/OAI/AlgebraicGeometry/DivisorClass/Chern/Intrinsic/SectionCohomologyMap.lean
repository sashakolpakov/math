import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ResolutionInjective
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.AugmentedResolution

/-! # Section Cohomology Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCohomologyMap

noncomputable section

/-! Native cohomology comparison on actual global sections of a degree-zero resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

def nativeInjectiveSectionCohomologyMap (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (injectiveResolution F).cocomplex).homology (n + 1) ⟶
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj F :=
  HomologicalComplex.homologyMap (GammaSectionsComparison.abelianGammaSectionsIso (injectiveResolution F).cocomplex).inv (n + 1) ≫
    (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom

theorem nativeInjectiveSectionCohomologyMap_class (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)
    (s : ((injectiveResolution F).cocomplex.X (n + 1)).obj.obj (op (⊤ : Opens X)))
    (hs : ((injectiveResolution F).cocomplex.d (n + 1) (n + 2)).hom.app (op (⊤ : Opens X)) s = 0) :
    nativeInjectiveSectionCohomologyMap F n
      ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (injectiveResolution F).cocomplex).homologyπ (n + 1)
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ s hs)) = Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (injectiveResolution F) (n + 1) s hs := by
  change (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom
    (HomologicalComplex.homologyMap (GammaSectionsComparison.abelianGammaSectionsIso (injectiveResolution F).cocomplex).inv (n + 1)
      ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (injectiveResolution F).cocomplex).homologyπ (n + 1)
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ s hs))) = _
  have hm := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n (GammaSectionsComparison.abelianGammaSectionsIso (injectiveResolution F).cocomplex).inv
    s hs (ResolutionInjective.nativeResolutionTopSection_closed F n s hs)
  exact (congrArg (fun x => (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom x) hm).trans
    (ResolutionInjective.nativeInjectiveCohomologyIso_sectionClass F n s hs)

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
  (he : ∀ q, K.ExactAt (q + 1))

def nativeSectionCohomologyMap (n : ℕ) :
    (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex K).homology (n + 1) ⟶
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj (K.homology 0) :=
  HomologicalComplex.homologyMap
      (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map
        (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (injectiveResolution (K.homology 0)))) (n + 1) ≫
    nativeInjectiveSectionCohomologyMap (K.homology 0) n

theorem nativeSectionCohomologyMap_class (n : ℕ)
    (s : (K.X (n + 1)).obj.obj (op (⊤ : Opens X)))
    (hs : (K.d (n + 1) (n + 2)).hom.app (op (⊤ : Opens X)) s = 0) :
    nativeSectionCohomologyMap K he n
      ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex K).homologyπ (n + 1) (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ s hs)) =
      Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (injectiveResolution (K.homology 0)) (n + 1)
        (((HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (injectiveResolution (K.homology 0))).f (n + 1)).hom.app (op (⊤ : Opens X)) s)
        (Chern.Sheaf.AugmentedResolution.sheafCochainMap_section_closed _ (n + 1) s hs) := by
  change nativeInjectiveSectionCohomologyMap (K.homology 0) n
    (HomologicalComplex.homologyMap
      (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map
        (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (injectiveResolution (K.homology 0)))) (n + 1)
      ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex K).homologyπ (n + 1) (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ s hs))) = _
  have hm := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n
    (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map
      (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (injectiveResolution (K.homology 0))))
    s hs (Chern.Sheaf.AugmentedResolution.sheafCochainMap_section_closed _ (n + 1) s hs)
  exact (congrArg (fun x => nativeInjectiveSectionCohomologyMap (K.homology 0) n x) hm).trans
    (nativeInjectiveSectionCohomologyMap_class _ _ _ _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCohomologyMap

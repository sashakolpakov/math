import OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueCechD
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueResolution

/-! # Gamma Sections Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GammaSectionsComparison

noncomputable section

section

/-! The native right-adjoint global sections and actual sections on the whole space agree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

def abelianGammaSectionsIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) :
    FlasqueCechD.abelianDerivedSectionsComplex K ≅ CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop).app (K.X n))
    (fun i j _ =>
      ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop).hom.naturality (K.d i j)).symm)

theorem abelianGammaSectionsIso_naturality
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L) :
    FlasqueCechD.abelianDerivedSectionsMap f ≫ (abelianGammaSectionsIso L).hom =
      (abelianGammaSectionsIso K).hom ≫
        ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop).hom.naturality (f.f n)

theorem abelianFlasqueGamma_quasiIso
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L)
    (hK : ∀ n, IsFlasque (K.X n)) (hL : ∀ n, IsFlasque (L.X n)) [QuasiIso f] :
    QuasiIso (FlasqueCechD.abelianDerivedSectionsMap f) := by
  have := Abelian.FlasqueComparison.abelianFlasqueGlobalSections_quasiIso f hK hL
  have he : FlasqueCechD.abelianDerivedSectionsMap f = (abelianGammaSectionsIso K).hom ≫
      ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (.up ℕ)).map f ≫
        (abelianGammaSectionsIso L).inv := by
    rw [← Category.assoc, (abelianGammaSectionsIso L).eq_comp_inv]
    exact abelianGammaSectionsIso_naturality f
  rw [he]
  infer_instance

end

/-! An actual flasque-resolution comparison with sheaf cohomology compatible with the Cech map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

local instance nativeFlasqueSections_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

def nativeInjectiveCohomologyIso (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    (FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex).homology (n + 1) ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj F := by
  letI : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive := nativeFlasqueSections_additive
  exact ((injectiveResolution F).isoRightDerivedObj (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).symm ≪≫
    (SheafCohomology.Cech.Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections F (n + 1)).symm.toAddCommGrpIso

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
  (hK : ∀ q, IsFlasque (K.X q)) (he : ∀ q, K.ExactAt (q + 1))

theorem nativeInjectiveResolution_flasque (q : ℕ) :
    IsFlasque ((injectiveResolution (K.homology 0)).cocomplex.X q) :=
  @SheafCohomology.Cech.Compat.TopCat.Sheaf.IsFlasque.of_injective X _ ((injectiveResolution (K.homology 0)).injective q)

include hK in
theorem nativeFlasqueResolutionLift_quasiIso :
    QuasiIso (FlasqueCechD.abelianDerivedSectionsMap (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (injectiveResolution (K.homology 0)))) := by
  have := HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift_quasiIso K he (injectiveResolution (K.homology 0))
  exact abelianFlasqueGamma_quasiIso _ hK (nativeInjectiveResolution_flasque K)

def nativeFlasqueCohomologyIso (n : ℕ) :
    (FlasqueCechD.abelianDerivedSectionsComplex K).homology (n + 1) ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj (K.homology 0) := by
  have := nativeFlasqueResolutionLift_quasiIso K hK he
  exact asIso (HomologicalComplex.homologyMap
      (FlasqueCechD.abelianDerivedSectionsMap (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (injectiveResolution (K.homology 0)))) (n + 1)) ≪≫
    nativeInjectiveCohomologyIso (K.homology 0) n

def nativeFlasqueCohomologyIsoOfZero (n : ℕ) {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    (e : F ≅ K.homology 0) :
    (FlasqueCechD.abelianDerivedSectionsComplex K).homology (n + 1) ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj F :=
  nativeFlasqueCohomologyIso K hK he n ≪≫
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).mapIso e).symm

theorem nativeFlasqueCohomologyIso_hom (n : ℕ) :
    (nativeFlasqueCohomologyIso K hK he n).hom =
      HomologicalComplex.homologyMap
        (FlasqueCechD.abelianDerivedSectionsMap (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he (injectiveResolution (K.homology 0)))) (n + 1) ≫
          (nativeInjectiveCohomologyIso (K.homology 0) n).hom := rfl

variable {I : Type} (U : I → Opens X) (hU : ⨆ i, U i = ⊤)

theorem nativeFlasqueCohomologyIso_cech (n : ℕ) :
    FlasqueCechD.abelianCechFlasqueComparison U hK ((HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0)
        (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.zeroAugmentationSequence K).zero hU n ≫ (nativeFlasqueCohomologyIso K hK he n).hom =
      Abelian.CechComparison.abelianCechToSheaf U (K.homology 0) hU n := by
  let R := injectiveResolution (K.homology 0)
  let f := HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he R
  have ha : (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0 ≫ f.f 0 = R.ι.f 0 :=
    congrArg (fun g => g.f 0) (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift_augmentation K he R)
  rw [nativeFlasqueCohomologyIso_hom, ← Category.assoc,
    FlasqueCechD.abelianCechFlasqueComparison_naturality U hK (nativeInjectiveResolution_flasque K)
      ((HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0) (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.zeroAugmentationSequence K).zero
      (R.ι.f 0) R.ι_f_zero_comp_complex_d f ha hU n]
  unfold FlasqueCechD.abelianCechFlasqueComparison nativeInjectiveCohomologyIso Abelian.CechComparison.abelianCechToSheaf Abelian.CechComparison.abelianCechToDerived
  simp only [Iso.trans_hom, Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GammaSectionsComparison

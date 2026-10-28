import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechComparison

/-! # Flasque Cech D -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueCechD

noncomputable section

section

/-! Global sections of any complex of flasque sheaves compute its native Cech total cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

local instance flasqueCechSections_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

def abelianDerivedSectionsComplex (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K

def abelianDerivedSectionsMap
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L) :
    abelianDerivedSectionsComplex K ⟶ abelianDerivedSectionsComplex L :=
  ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map f

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)

def abelianCechHorizontalAugmentation (q : ℕ) :
    (abelianDerivedSectionsComplex K).X q ⟶ ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X q).X 0 :=
  SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (K.X q) U

theorem abelianCechHorizontalAugmentation_comm (q q' : ℕ)
    (_ : (ComplexShape.up ℕ).Rel q q') :
    abelianCechHorizontalAugmentation U K q ≫ ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).d q q').f 0 =
      (abelianDerivedSectionsComplex K).d q q' ≫ abelianCechHorizontalAugmentation U K q' := by
  change SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (K.X q) U ≫
      ((CategoryTheory.cechComplexFunctor U).map (K.d q q').hom).f 0 =
    (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (K.d q q') ≫ SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (K.X q') U
  exact SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_naturality (U := U) (F := K.X q) (K.d q q')

theorem abelianCechHorizontalAugmentation_d (q : ℕ) :
    abelianCechHorizontalAugmentation U K q ≫ ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X q).d 0 1 = 0 :=
  SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d (K.X q) U

def abelianCechHorizontalEdge :
    abelianDerivedSectionsComplex K ⟶ (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).total (.up ℕ) :=
  (SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge
    (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K))
    (abelianDerivedSectionsComplex K)
    (abelianCechHorizontalAugmentation U K) (abelianCechHorizontalAugmentation_comm U K)
    (abelianCechHorizontalAugmentation_d U K)

theorem abelianCechHorizontalEdge_f (q : ℕ) :
    (abelianCechHorizontalEdge U K).f q =
      abelianCechHorizontalAugmentation U K q ≫ (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).ιTotal (.up ℕ) q 0 q rfl :=
  SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f _ _ _ _ _ q

theorem abelianFlasqueCech_rowsExact (hK : ∀ q, IsFlasque (K.X q))
    (hU : ⨆ i, U i = ⊤) : SheafCohomology.Cech.ComplexUpNatNormalize.Projective.RowsExact (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K) := by
  intro q p
  have := hK q
  apply (HomologicalComplex.exactAt_iff' ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).X q)
    p (p + 1) (p + 2) (by simp) (by simp)).1
  exact SheafCohomology.Cech.FlasqueExact.TopCat.Sheaf.cechComplex_exactAt_succ_of_isFlasque (K.X q) U hU p

theorem abelianFlasqueCechHorizontalEdge_quasiIsoAt (hK : ∀ q, IsFlasque (K.X q))
    (hU : ⨆ i, U i = ⊤) (n : ℕ) : QuasiIsoAt (abelianCechHorizontalEdge U K) (n + 1) := by
  apply SheafCohomology.Cech.ComplexUpNatComparison.Projective.horizontal_edge_quasiIsoAt
  · intro q
    exact SheafCohomology.Cech.InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsNativeShortComplex_exact U (K.X q) hU
  · intro q
    exact SheafCohomology.Cech.InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsAugmentation_mono U (K.X q) hU
  · exact abelianFlasqueCech_rowsExact U K hK hU

def abelianFlasqueCechHomologyIso (hK : ∀ q, IsFlasque (K.X q))
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (abelianDerivedSectionsComplex K).homology (n + 1) ≅
      ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).total (.up ℕ)).homology (n + 1) := by
  have := abelianFlasqueCechHorizontalEdge_quasiIsoAt U K hK hU n
  exact asIso (HomologicalComplex.homologyMap (abelianCechHorizontalEdge U K) (n + 1))

end

section

/-! Naturality of both native Cech edges for actual maps of sheaf complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}

def abelianCechBicomplexMap (f : K ⟶ L) : SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K ⟶ SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U L :=
  ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).mapHomologicalComplex (.up ℕ)).map f

def abelianCechTotalMap (f : K ⟶ L) :
    (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).total (.up ℕ) ⟶ (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U L).total (.up ℕ) :=
  HomologicalComplex₂.total.map (abelianCechBicomplexMap U f) (.up ℕ)

theorem abelianCechHorizontalEdge_naturality (f : K ⟶ L) :
    abelianDerivedSectionsMap f ≫ abelianCechHorizontalEdge U L =
      abelianCechHorizontalEdge U K ≫ abelianCechTotalMap U f := by
  apply HomologicalComplex.Hom.ext
  funext q
  have hAug : abelianCechHorizontalAugmentation U K q ≫
        ((abelianCechBicomplexMap U f).f q).f 0 =
      (abelianDerivedSectionsMap f).f q ≫ abelianCechHorizontalAugmentation U L q :=
    SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_naturality (U := U) (f := f.f q)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    abelianCechHorizontalEdge_f, abelianCechHorizontalEdge_f,
    Category.assoc, abelianCechTotalMap, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc (abelianCechHorizontalAugmentation U K q), hAug, Category.assoc]

variable {F : TopCat.Sheaf AddCommGrpCat.{0} X} (a : F ⟶ K.X 0)
  (ha : a ≫ K.d 0 1 = 0)

include ha in
theorem abelianCechVerticalAugmentation_d (p : ℕ) :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map a).f p ≫ ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).d 0 1).f p = 0 := by
  have h : (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map a ≫ (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (K.d 0 1) = 0 := by
    rw [← Functor.map_comp, ha, Functor.map_zero]
  exact congrArg (fun f => f.f p) h

def abelianCechVerticalEdge :
    (CategoryTheory.cechComplexFunctor U).obj F.obj ⟶ (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).total (.up ℕ) :=
  (SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge
    (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K))
    ((CategoryTheory.cechComplexFunctor U).obj F.obj)
    (fun p => ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map a).f p)
    (fun p p' _ => ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map a).comm p p')
    (abelianCechVerticalAugmentation_d U a ha)

theorem abelianCechVerticalEdge_f (p : ℕ) :
    (abelianCechVerticalEdge U a ha).f p =
      ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map a).f p ≫
        (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).ιTotal (.up ℕ) 0 p p (Nat.zero_add p) :=
  SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge_f _ _ _ _ _ p

theorem abelianCechVerticalEdge_naturality (f : K ⟶ L)
    (b : F ⟶ L.X 0) (hb : b ≫ L.d 0 1 = 0) (hab : a ≫ f.f 0 = b) :
    abelianCechVerticalEdge U a ha ≫ abelianCechTotalMap U f =
      abelianCechVerticalEdge U b hb := by
  apply HomologicalComplex.Hom.ext
  funext p
  rw [HomologicalComplex.comp_f, abelianCechVerticalEdge_f, abelianCechVerticalEdge_f,
    Category.assoc, abelianCechTotalMap, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  congr 1
  change (((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map a).f p ≫
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map (f.f 0)).f p) = ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map b).f p
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, hab]

end

/-! Compare a concrete Cech cocycle with any actual flasque resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {F : TopCat.Sheaf AddCommGrpCat.{0} X}

def abelianCechFlasqueComparison (hK : ∀ q, IsFlasque (K.X q))
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj F.obj).homology (n + 1) ⟶
      (abelianDerivedSectionsComplex K).homology (n + 1) :=
  HomologicalComplex.homologyMap (abelianCechVerticalEdge U a ha) (n + 1) ≫
    (abelianFlasqueCechHomologyIso U K hK hU n).inv

theorem abelianCechFlasqueComparison_naturality
    (hK : ∀ q, IsFlasque (K.X q)) (hL : ∀ q, IsFlasque (L.X q))
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (b : F ⟶ L.X 0) (hb : b ≫ L.d 0 1 = 0)
    (f : K ⟶ L) (hab : a ≫ f.f 0 = b) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    abelianCechFlasqueComparison U hK a ha hU n ≫
        HomologicalComplex.homologyMap (abelianDerivedSectionsMap f) (n + 1) =
      abelianCechFlasqueComparison U hL b hb hU n := by
  have hh : HomologicalComplex.homologyMap (abelianDerivedSectionsMap f) (n + 1) ≫
        (abelianFlasqueCechHomologyIso U L hL hU n).hom =
      (abelianFlasqueCechHomologyIso U K hK hU n).hom ≫
        HomologicalComplex.homologyMap (abelianCechTotalMap U f) (n + 1) := by
    change HomologicalComplex.homologyMap (abelianDerivedSectionsMap f) (n + 1) ≫
        HomologicalComplex.homologyMap (abelianCechHorizontalEdge U L) (n + 1) =
      HomologicalComplex.homologyMap (abelianCechHorizontalEdge U K) (n + 1) ≫
        HomologicalComplex.homologyMap (abelianCechTotalMap U f) (n + 1)
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      abelianCechHorizontalEdge_naturality]
  have hi : (abelianFlasqueCechHomologyIso U K hK hU n).inv ≫
        HomologicalComplex.homologyMap (abelianDerivedSectionsMap f) (n + 1) =
      HomologicalComplex.homologyMap (abelianCechTotalMap U f) (n + 1) ≫
        (abelianFlasqueCechHomologyIso U L hL hU n).inv := by
    rw [(abelianFlasqueCechHomologyIso U L hL hU n).eq_comp_inv, Category.assoc, hh]
    simp
  unfold abelianCechFlasqueComparison
  rw [Category.assoc, hi, ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    abelianCechVerticalEdge_naturality U a ha f b hb hab]

theorem abelianCechVerticalEdge_injective (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    abelianCechVerticalEdge U ((injectiveResolution F).ι.f 0)
        (injectiveResolution F).ι_f_zero_comp_complex_d =
      SheafCohomology.Cech.InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U F := by
  rfl

theorem abelianCechHorizontalEdge_injective (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    abelianCechHorizontalEdge U (injectiveResolution F).cocomplex =
      SheafCohomology.Cech.HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge U F := by
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueCechD

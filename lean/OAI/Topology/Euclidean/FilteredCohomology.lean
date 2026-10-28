import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Filtered Cohomology -/

namespace OAI.Topology.Euclidean.FilteredCohomology.Globalization

noncomputable section

section

/-!
# Cohomology and filtered colimits of actual module complexes

The comparison is constructed from exactness of filtered colimits of modules.
Its compatibility with the actual stage inclusions identifies it with the
canonical cohomology comparison, ready for compact-support cochain diagrams.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R : Type} [Ring R] {J : Type} [SmallCategory J]

/-- A diagram of actual cochain complexes, read as a cochain complex of
module-valued functors. -/
def cochainDiagramComplex (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) :
    CochainComplex (J ⥤ ModuleCat.{0} R) ℕ where
  X n := F ⋙ HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n
  d n m :=
    { app j := (F.obj j).d n m
      naturality _ _ f := (F.map f).comm n m }
  shape n m h := by
    apply NatTrans.ext
    funext j
    exact (F.obj j).shape n m h
  d_comp_d' n m k _ _ := by
    apply NatTrans.ext
    funext j
    exact (F.obj j).d_comp_d n m k

/-- The genuine degreewise colimit complex. -/
abbrev pointwiseColimitComplex (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (HomologicalComplex.coconeOfHasColimitEval F).pt

/-- Inclusion of a stage in the degreewise colimit complex. -/
abbrev pointwiseColimitStage (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (j : J) :
    F.obj j ⟶ pointwiseColimitComplex F :=
  (HomologicalComplex.coconeOfHasColimitEval F).ι.app j

/-- The degreewise colimit is canonically isomorphic to the categorical
colimit in the category of cochain complexes. -/
def pointwiseColimitIso (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) :
    pointwiseColimitComplex F ≅ colimit F :=
  (HomologicalComplex.isColimitCoconeOfHasColimitEval F).coconePointUniqueUpToIso
    (colimit.isColimit F)

@[reassoc (attr := simp)]
theorem pointwiseColimitStage_iso (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (j : J) :
    pointwiseColimitStage F j ≫ (pointwiseColimitIso F).hom = colimit.ι F j := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (HomologicalComplex.isColimitCoconeOfHasColimitEval F) (colimit.isColimit F) j

/-- The actual stage inclusion is natural in a diagram of modules. -/
def moduleColimitInjection (j : J) :
    (evaluation J (ModuleCat.{0} R)).obj j ⟶ (colim : (J ⥤ ModuleCat.{0} R) ⥤ _) where
  app F := colimit.ι F j
  naturality _ _ f := (ι_colimMap f j).symm

set_option backward.isDefEq.respectTransparency false in
/-- Homology of a complex of functors is naturally its stagewise cohomology. -/
def diagramCohomologyIso (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n ≅
      (cochainDiagramComplex F).homology n :=
  NatIso.ofComponents
    (fun j => ((cochainDiagramComplex F).sc n).mapHomologyIso
      ((evaluation J (ModuleCat.{0} R)).obj j))
    (fun {j k} f => by
      let τ := (evaluation J (ModuleCat.{0} R)).map f
      change ShortComplex.homologyMap ((cochainDiagramComplex F).sc n |>.mapNatTrans τ) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl)

variable [IsFiltered J]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of filtered module colimits gives the cohomology comparison for
the genuine degreewise colimit complex. -/
def pointwiseColimitCohomologyIso
    (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (pointwiseColimitComplex F).homology n ≅ colimit ((cochainDiagramComplex F).homology n) :=
  ((cochainDiagramComplex F).sc n).mapHomologyIso
    (colim : (J ⥤ ModuleCat.{0} R) ⥤ ModuleCat.{0} R)

set_option backward.isDefEq.respectTransparency false in
/-- Stage maps commute with the comparison obtained from exactness. -/
@[reassoc]
theorem pointwiseColimitStage_homology
    (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (j : J) :
    HomologicalComplex.homologyMap (pointwiseColimitStage F j) n ≫
        (pointwiseColimitCohomologyIso F n).hom =
      (diagramCohomologyIso F n).hom.app j ≫
        colimit.ι ((cochainDiagramComplex F).homology n) j := by
  change ShortComplex.homologyMap
    ((cochainDiagramComplex F).sc n |>.mapNatTrans (moduleColimitInjection (R := R) j)) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [pointwiseColimitCohomologyIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The canonical comparison from the filtered colimit of stage cohomology to
the cohomology of the actual categorical colimit complex. -/
def filteredCohomologyComparisonIso
    (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    colimit (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n) ≅
      (colimit F).homology n :=
  (colim : (J ⥤ ModuleCat.{0} R) ⥤ ModuleCat.{0} R).mapIso (diagramCohomologyIso F n) ≪≫
    (pointwiseColimitCohomologyIso F n).symm ≪≫
      HomologicalComplex.homologyMapIso (pointwiseColimitIso F) n

set_option backward.isDefEq.respectTransparency false in
/-- The cohomology comparison is characterized by the actual stage maps. -/
@[reassoc (attr := simp)]
theorem filteredCohomologyComparisonIso_ι
    (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (j : J) :
    colimit.ι (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        (ComplexShape.up ℕ) n) j ≫ (filteredCohomologyComparisonIso F n).hom =
      HomologicalComplex.homologyMap (colimit.ι F j) n := by
  change colimit.ι _ j ≫ colimMap (diagramCohomologyIso F n).hom ≫
    (pointwiseColimitCohomologyIso F n).inv ≫
      HomologicalComplex.homologyMap (pointwiseColimitIso F).hom n = _
  rw [ι_colimMap_assoc, ← pointwiseColimitStage_homology_assoc,
    Iso.hom_inv_id_assoc, ← HomologicalComplex.homologyMap_comp, pointwiseColimitStage_iso]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism is literally the standard categorical comparison map. -/
theorem filteredCohomologyComparisonIso_hom
    (F : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (filteredCohomologyComparisonIso F n).hom =
      colimit.post F (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        (ComplexShape.up ℕ) n) := by
  apply colimit.hom_ext
  intro j
  rw [filteredCohomologyComparisonIso_ι, colimit.ι_post]
  rfl

/-- The actual cohomology functor preserves filtered colimits of modules. -/
instance cohomology_preservesFilteredColimitsOfShape (n : ℕ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n) where
  preservesColimit {F} := by
    have : IsIso (colimit.post F (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        (ComplexShape.up ℕ) n)) := by
      rw [← filteredCohomologyComparisonIso_hom]
      exact (filteredCohomologyComparisonIso F n).isIso_hom
    exact preservesColimit_of_isIso_post _ F

set_option backward.isDefEq.respectTransparency false in
/-- The filtered comparison commutes with every actual morphism of diagrams. -/
@[reassoc]
theorem filteredCohomologyComparisonIso_naturality
    {F G : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ} (f : F ⟶ G) (n : ℕ) :
    colimMap (Functor.whiskerRight f (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        (ComplexShape.up ℕ) n)) ≫ (filteredCohomologyComparisonIso G n).hom =
      (filteredCohomologyComparisonIso F n).hom ≫
        HomologicalComplex.homologyMap (colimMap f) n := by
  rw [filteredCohomologyComparisonIso_hom, filteredCohomologyComparisonIso_hom]
  exact (colimit.map_post f _).symm

set_option backward.isDefEq.respectTransparency false in
/-- A filtered colimit of quasi-isomorphisms of actual module complexes is a
quasi-isomorphism. This permits stagewise comparisons of support complexes. -/
theorem filteredColimit_quasiIso
    {F G : J ⥤ CochainComplex (ModuleCat.{0} R) ℕ} (f : F ⟶ G)
    [∀ j, QuasiIso (f.app j)] : QuasiIso (colimMap f) := by
  constructor
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).mpr
  have : IsIso (Functor.whiskerRight f (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
      (ComplexShape.up ℕ) n)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro j
    change IsIso (HomologicalComplex.homologyMap (f.app j) n)
    infer_instance
  apply (isIso_comp_left_iff (filteredCohomologyComparisonIso F n).hom _).mp
  rw [← filteredCohomologyComparisonIso_naturality]
  infer_instance

end

/-!
# Filtered homology comparison for arbitrary complex shapes

This extends the verified cochain argument to every actual homological
complex shape, including ordinary chain complexes. It reuses the genuine
module colimit injections and the same mathlib exact-functor construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R : Type} [Ring R] {J : Type} [SmallCategory J]
  {I : Type} {c : ComplexShape I}

/-- A diagram of actual homological complexes, read as a homological complex of
module-valued functors. -/
def homologicalDiagramComplex (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) :
    HomologicalComplex (J ⥤ ModuleCat.{0} R) c where
  X n := F ⋙ HomologicalComplex.eval (ModuleCat.{0} R) c n
  d n m :=
    { app j := (F.obj j).d n m
      naturality _ _ f := (F.map f).comm n m }
  shape n m h := by
    apply NatTrans.ext
    funext j
    exact (F.obj j).shape n m h
  d_comp_d' n m k _ _ := by
    apply NatTrans.ext
    funext j
    exact (F.obj j).d_comp_d n m k

/-- The genuine degreewise colimit complex. -/
abbrev degreewiseColimitComplex (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) :
    HomologicalComplex (ModuleCat.{0} R) c :=
  (HomologicalComplex.coconeOfHasColimitEval F).pt

/-- Inclusion of a stage in the degreewise colimit complex. -/
abbrev degreewiseColimitStage (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) (j : J) :
    F.obj j ⟶ degreewiseColimitComplex F :=
  (HomologicalComplex.coconeOfHasColimitEval F).ι.app j

/-- The degreewise colimit is canonically isomorphic to the categorical
colimit in the category of homological complexes. -/
def degreewiseColimitIso (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) :
    degreewiseColimitComplex F ≅ colimit F :=
  (HomologicalComplex.isColimitCoconeOfHasColimitEval F).coconePointUniqueUpToIso
    (colimit.isColimit F)

@[reassoc (attr := simp)]
theorem degreewiseColimitStage_iso (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) (j : J) :
    degreewiseColimitStage F j ≫ (degreewiseColimitIso F).hom = colimit.ι F j := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (HomologicalComplex.isColimitCoconeOfHasColimitEval F) (colimit.isColimit F) j

set_option backward.isDefEq.respectTransparency false in
/-- Homology of a complex of functors is naturally its stagewise homology. -/
def diagramHomologyIso (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) (n : I) :
    F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} R) c n ≅
      (homologicalDiagramComplex F).homology n :=
  NatIso.ofComponents
    (fun j => ((homologicalDiagramComplex F).sc n).mapHomologyIso
      ((evaluation J (ModuleCat.{0} R)).obj j))
    (fun {j k} f => by
      let τ := (evaluation J (ModuleCat.{0} R)).map f
      change ShortComplex.homologyMap ((homologicalDiagramComplex F).sc n |>.mapNatTrans τ) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl)

variable [IsFiltered J]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of filtered module colimits gives the homology comparison for
the genuine degreewise colimit complex. -/
def degreewiseColimitHomologyIso
    (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) (n : I) :
    (degreewiseColimitComplex F).homology n ≅ colimit ((homologicalDiagramComplex F).homology n) :=
  ((homologicalDiagramComplex F).sc n).mapHomologyIso
    (colim : (J ⥤ ModuleCat.{0} R) ⥤ ModuleCat.{0} R)

set_option backward.isDefEq.respectTransparency false in
/-- Stage maps commute with the comparison obtained from exactness. -/
@[reassoc]
theorem degreewiseColimitStage_homology
    (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) (n : I) (j : J) :
    HomologicalComplex.homologyMap (degreewiseColimitStage F j) n ≫
        (degreewiseColimitHomologyIso F n).hom =
      (diagramHomologyIso F n).hom.app j ≫
        colimit.ι ((homologicalDiagramComplex F).homology n) j := by
  change ShortComplex.homologyMap
    ((homologicalDiagramComplex F).sc n |>.mapNatTrans (moduleColimitInjection (R := R) j)) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [degreewiseColimitHomologyIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The canonical comparison from the filtered colimit of stage homology to
the homology of the actual categorical colimit complex. -/
def filteredHomologyComparisonIso
    (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) (n : I) :
    colimit (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} R) c n) ≅
      (colimit F).homology n :=
  (colim : (J ⥤ ModuleCat.{0} R) ⥤ ModuleCat.{0} R).mapIso (diagramHomologyIso F n) ≪≫
    (degreewiseColimitHomologyIso F n).symm ≪≫
      HomologicalComplex.homologyMapIso (degreewiseColimitIso F) n

set_option backward.isDefEq.respectTransparency false in
/-- The homology comparison is characterized by the actual stage maps. -/
@[reassoc (attr := simp)]
theorem filteredHomologyComparisonIso_ι
    (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) (n : I) (j : J) :
    colimit.ι (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        c n) j ≫ (filteredHomologyComparisonIso F n).hom =
      HomologicalComplex.homologyMap (colimit.ι F j) n := by
  change colimit.ι _ j ≫ colimMap (diagramHomologyIso F n).hom ≫
    (degreewiseColimitHomologyIso F n).inv ≫
      HomologicalComplex.homologyMap (degreewiseColimitIso F).hom n = _
  rw [ι_colimMap_assoc, ← degreewiseColimitStage_homology_assoc,
    Iso.hom_inv_id_assoc, ← HomologicalComplex.homologyMap_comp, degreewiseColimitStage_iso]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism is literally the standard categorical comparison map. -/
theorem filteredHomologyComparisonIso_hom
    (F : J ⥤ HomologicalComplex (ModuleCat.{0} R) c) (n : I) :
    (filteredHomologyComparisonIso F n).hom =
      colimit.post F (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        c n) := by
  apply colimit.hom_ext
  intro j
  rw [filteredHomologyComparisonIso_ι, colimit.ι_post]
  rfl

/-- The actual homology functor preserves filtered colimits of modules. -/
instance homology_preservesFilteredColimitsOfShape (n : I) :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) c n) where
  preservesColimit {F} := by
    have : IsIso (colimit.post F (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        c n)) := by
      rw [← filteredHomologyComparisonIso_hom]
      exact (filteredHomologyComparisonIso F n).isIso_hom
    exact preservesColimit_of_isIso_post _ F

set_option backward.isDefEq.respectTransparency false in
/-- The filtered comparison commutes with every actual morphism of diagrams. -/
@[reassoc]
theorem filteredHomologyComparisonIso_naturality
    {F G : J ⥤ HomologicalComplex (ModuleCat.{0} R) c} (f : F ⟶ G) (n : I) :
    colimMap (Functor.whiskerRight f (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
        c n)) ≫ (filteredHomologyComparisonIso G n).hom =
      (filteredHomologyComparisonIso F n).hom ≫
        HomologicalComplex.homologyMap (colimMap f) n := by
  rw [filteredHomologyComparisonIso_hom, filteredHomologyComparisonIso_hom]
  exact (colimit.map_post f _).symm

set_option backward.isDefEq.respectTransparency false in
/-- A filtered colimit of quasi-isomorphisms of actual module complexes is a
quasi-isomorphism. This permits stagewise comparisons of support complexes. -/
theorem filteredHomologyColimit_quasiIso
    {F G : J ⥤ HomologicalComplex (ModuleCat.{0} R) c} (f : F ⟶ G)
    [∀ j, QuasiIso (f.app j)] : QuasiIso (colimMap f) := by
  constructor
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).mpr
  have : IsIso (Functor.whiskerRight f (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
      c n)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro j
    change IsIso (HomologicalComplex.homologyMap (f.app j) n)
    infer_instance
  apply (isIso_comp_left_iff (filteredHomologyComparisonIso F n).hom _).mp
  rw [← filteredHomologyComparisonIso_naturality]
  infer_instance

end

end OAI.Topology.Euclidean.FilteredCohomology.Globalization

import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorFunctoriality

/-! # Tensor Unit -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction

noncomputable section

/-! Unit compatibility for the tensor comparison maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance tensorUnitMonoidal (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

theorem sheafTensorHomEquiv_apply_eq {X : Scheme.{u}} {M N P : X.Modules}
    (h : SheafTensor.Construction.sheafTensor M N ⟶ P) :
    SheafTensor.Construction.sheafTensorHomEquiv M N P h = SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val) ≫ h.val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit _ _ h

theorem sheafTensorHomEquiv_unitLeft {X : Scheme.{u}} (M : X.Modules) :
    SheafTensor.Construction.sheafTensorHomEquiv (LineBundle.Construction.structureSheafModule X) M M (SheafTensor.Construction.sheafTensorUnitLeft M).hom =
      (λ_ M.val).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv _ M (F.map (λ_ M.val).hom ≫ adj.counit.app M) = (λ_ M.val).hom
  have hc : adj.homEquiv _ M (adj.counit.app M) = 𝟙 M.val :=
    (congrArg (adj.homEquiv _ M) (adj.homEquiv_symm_id M)).symm.trans
      ((adj.homEquiv _ M).apply_symm_apply _)
  exact (adj.homEquiv_naturality_left (λ_ M.val).hom (adj.counit.app M)).trans
    ((congrArg (fun q ↦ (λ_ M.val).hom ≫ q) hc).trans (Category.comp_id _))

theorem moduleSheafificationUnit_unitLeft {X : Scheme.{u}} (M : X.Modules) :
    SheafRestriction.Construction.moduleSheafificationUnit ((LineBundle.Construction.structureSheafModule X).val ⊗ M.val) ≫
      (SheafTensor.Construction.sheafTensorUnitLeft M).hom.val = (λ_ M.val).hom :=
  (sheafTensorHomEquiv_apply_eq (SheafTensor.Construction.sheafTensorUnitLeft M).hom).symm.trans
    (sheafTensorHomEquiv_unitLeft M)

def structureSheafToPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LineBundle.Construction.structureSheafModule Y ⟶ (Scheme.Modules.pushforward f).obj (LineBundle.Construction.structureSheafModule X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

theorem pushforwardPresheafTensorMap_units {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((structureSheafToPushforward f).val ⊗ₘ (structureSheafToPushforward f).val) ≫
      TensorFunctoriality.Construction.pushforwardPresheafTensorMap f (LineBundle.Construction.structureSheafModule X).val (LineBundle.Construction.structureSheafModule X).val ≫
        (TensorFunctoriality.Construction.pushforwardModulePresheaf f).map (λ_ (LineBundle.Construction.structureSheafModule X).val).hom =
    (λ_ (LineBundle.Construction.structureSheafModule Y).val).hom ≫ (structureSheafToPushforward f).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  exact ((f.app U.unop).hom.map_mul a b).symm

theorem pushforwardSheafTensorMap_units {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TensorFunctoriality.Construction.sheafTensorMap (structureSheafToPushforward f) (structureSheafToPushforward f) ≫
      TensorFunctoriality.Construction.pushforwardSheafTensorMap f (LineBundle.Construction.structureSheafModule X) (LineBundle.Construction.structureSheafModule X)) ≫
        (Scheme.Modules.pushforward f).map (SheafTensor.Construction.sheafTensorUnitLeft (LineBundle.Construction.structureSheafModule X)).hom =
    (SheafTensor.Construction.sheafTensorUnitLeft (LineBundle.Construction.structureSheafModule Y)).hom ≫ structureSheafToPushforward f := by
  apply (SheafTensor.Construction.sheafTensorHomEquiv _ _ _).injective
  rw [TensorFunctoriality.Construction.sheafTensorHomEquiv_naturality_right, TensorFunctoriality.Construction.sheafTensorHomEquiv_naturality_left,
    TensorFunctoriality.Construction.sheafTensorHomEquiv_naturality_right, sheafTensorHomEquiv_unitLeft]
  simp only [TensorFunctoriality.Construction.pushforwardSheafTensorMap, Equiv.apply_symm_apply]
  let F := TensorFunctoriality.Construction.pushforwardModulePresheaf f
  let η := SheafRestriction.Construction.moduleSheafificationUnit ((LineBundle.Construction.structureSheafModule X).val ⊗ (LineBundle.Construction.structureSheafModule X).val)
  let l := (SheafTensor.Construction.sheafTensorUnitLeft (LineBundle.Construction.structureSheafModule X)).hom.val
  let q := TensorFunctoriality.Construction.pushforwardPresheafTensorMap f (LineBundle.Construction.structureSheafModule X).val (LineBundle.Construction.structureSheafModule X).val
  let t := (structureSheafToPushforward f).val ⊗ₘ (structureSheafToPushforward f).val
  have hmap : F.map η ≫ F.map l = F.map (λ_ (LineBundle.Construction.structureSheafModule X).val).hom :=
    (F.map_comp η l).symm.trans (congrArg F.map (moduleSheafificationUnit_unitLeft _))
  change (t ≫ (q ≫ F.map η)) ≫ F.map l = _
  exact (Category.assoc t (q ≫ F.map η) (F.map l)).trans
    ((congrArg (fun m ↦ t ≫ m) (Category.assoc q (F.map η) (F.map l))).trans
      ((congrArg (fun m ↦ t ≫ q ≫ m) hmap).trans (pushforwardPresheafTensorMap_units f)))

theorem pullbackStructureSheafIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (LineBundle.Construction.structureSheafModule Y) ≫
      (Scheme.Modules.pushforward f).map (LineBundle.Construction.pullbackStructureSheafIso f).hom =
        structureSheafToPushforward f := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have he : adj.homEquiv (LineBundle.Construction.structureSheafModule Y) (LineBundle.Construction.structureSheafModule X)
      (LineBundle.Construction.pullbackStructureSheafIso f).hom = structureSheafToPushforward f :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom
  exact (adj.homEquiv_unit _ _ _).symm.trans he

theorem pullbackSheafTensorMap_units {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TensorFunctoriality.Construction.pullbackSheafTensorMap f (LineBundle.Construction.structureSheafModule Y) (LineBundle.Construction.structureSheafModule Y) ≫
      TensorFunctoriality.Construction.sheafTensorMap (LineBundle.Construction.pullbackStructureSheafIso f).hom (LineBundle.Construction.pullbackStructureSheafIso f).hom) ≫
        (SheafTensor.Construction.sheafTensorUnitLeft (LineBundle.Construction.structureSheafModule X)).hom =
    (Scheme.Modules.pullback f).map (SheafTensor.Construction.sheafTensorUnitLeft (LineBundle.Construction.structureSheafModule Y)).hom ≫
      (LineBundle.Construction.pullbackStructureSheafIso f).hom := by
  let L := Scheme.Modules.pullback f
  let R := Scheme.Modules.pushforward f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let u := LineBundle.Construction.structureSheafModule Y
  let v := LineBundle.Construction.structureSheafModule X
  let e := LineBundle.Construction.pullbackStructureSheafIso f
  have he : adj.homEquiv u v e.hom = structureSheafToPushforward f :=
    (adj.homEquiv_unit _ _ _).trans (pullbackStructureSheafIso_unit f)
  have hq :
      (TensorFunctoriality.Construction.sheafTensorMap (adj.unit.app u) (adj.unit.app u) ≫
        TensorFunctoriality.Construction.pushforwardSheafTensorMap f (L.obj u) (L.obj u)) ≫ R.map (TensorFunctoriality.Construction.sheafTensorMap e.hom e.hom) =
      TensorFunctoriality.Construction.sheafTensorMap (structureSheafToPushforward f) (structureSheafToPushforward f) ≫
        TensorFunctoriality.Construction.pushforwardSheafTensorMap f v v := by
    rw [Category.assoc, TensorFunctoriality.Construction.pushforwardSheafTensorMap_naturality, ← Category.assoc,
      ← TensorFunctoriality.Construction.sheafTensorMap_comp, pullbackStructureSheafIso_unit]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right,
    adj.homEquiv_naturality_left]
  simp only [TensorFunctoriality.Construction.pullbackSheafTensorMap, adj, Equiv.apply_symm_apply]
  change ((TensorFunctoriality.Construction.sheafTensorMap (adj.unit.app u) (adj.unit.app u) ≫
    TensorFunctoriality.Construction.pushforwardSheafTensorMap f (L.obj u) (L.obj u)) ≫ R.map (TensorFunctoriality.Construction.sheafTensorMap e.hom e.hom)) ≫
      R.map (SheafTensor.Construction.sheafTensorUnitLeft v).hom = (SheafTensor.Construction.sheafTensorUnitLeft u).hom ≫ adj.homEquiv u v e.hom
  rw [hq, he]
  exact pushforwardSheafTensorMap_units f

theorem sheafTensorMap_isIso {X : Scheme.{u}} {M M' N N' : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') [IsIso a] [IsIso b] : IsIso (TensorFunctoriality.Construction.sheafTensorMap a b) :=
  (SheafTensor.Construction.sheafTensorCongr (asIso a) (asIso b)).isIso_hom

theorem isIso_pullbackSheafTensorMap_units {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f (LineBundle.Construction.structureSheafModule Y) (LineBundle.Construction.structureSheafModule Y)) := by
  let q := TensorFunctoriality.Construction.pullbackSheafTensorMap f (LineBundle.Construction.structureSheafModule Y) (LineBundle.Construction.structureSheafModule Y)
  let e := LineBundle.Construction.pullbackStructureSheafIso f
  let l := SheafTensor.Construction.sheafTensorUnitLeft (LineBundle.Construction.structureSheafModule X)
  have : IsIso (TensorFunctoriality.Construction.sheafTensorMap e.hom e.hom) := sheafTensorMap_isIso _ _
  have h : IsIso ((q ≫ TensorFunctoriality.Construction.sheafTensorMap e.hom e.hom) ≫ l.hom) := by
    rw [pullbackSheafTensorMap_units]
    infer_instance
  have : IsIso (q ≫ TensorFunctoriality.Construction.sheafTensorMap e.hom e.hom) := IsIso.of_isIso_comp_right _ l.hom
  exact IsIso.of_isIso_comp_right _ (TensorFunctoriality.Construction.sheafTensorMap e.hom e.hom)

/-- The pullback tensor comparison is invertible for globally trivial line bundles. -/
theorem isIso_pullbackSheafTensorMap_of_trivial {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (eM : M ≅ LineBundle.Construction.structureSheafModule Y) (eN : N ≅ LineBundle.Construction.structureSheafModule Y) :
    IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f M N) := by
  let L := Scheme.Modules.pullback f
  have : IsIso (TensorFunctoriality.Construction.sheafTensorMap eM.hom eN.hom) := sheafTensorMap_isIso _ _
  have : IsIso (TensorFunctoriality.Construction.sheafTensorMap (L.map eM.hom) (L.map eN.hom)) := sheafTensorMap_isIso _ _
  have := isIso_pullbackSheafTensorMap_units f
  have h : IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f M N ≫
      TensorFunctoriality.Construction.sheafTensorMap (L.map eM.hom) (L.map eN.hom)) := by
    rw [← TensorFunctoriality.Construction.pullbackSheafTensorMap_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (TensorFunctoriality.Construction.sheafTensorMap (L.map eM.hom) (L.map eN.hom))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction

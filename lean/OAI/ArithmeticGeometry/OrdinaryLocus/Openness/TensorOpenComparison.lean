import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorComposition
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction

/-! # Tensor Open Comparison -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorOpenComparison.Construction

noncomputable section

/-! The canonical pullback tensor comparison on open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance tensorOpenComparisonMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

theorem moduleSheafificationUnit_isoOfLocallyBijective {X : Scheme.{u}}
    {P : X.PresheafOfModules} {M : X.Modules} (q : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective (_root_.Opens.grothendieckTopology X) q]
    [PresheafOfModules.IsLocallySurjective (_root_.Opens.grothendieckTopology X) q] :
    SheafRestriction.Construction.moduleSheafificationUnit P ≫ (SheafRestriction.Construction.sheafificationIsoOfLocallyBijective q).hom.val = q := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let L : X.PresheafOfModules ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let R := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  change adj.unit.app P ≫ R.map (L.map q ≫ adj.counit.app M) = q
  exact (adj.homEquiv_unit _ _ _).symm.trans
    ((congrArg (adj.homEquiv _ _) (adj.homEquiv_counit _ _ q).symm).trans
      ((adj.homEquiv _ _).apply_symm_apply q))

theorem moduleSheafificationUnit_restrictIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (P : Y.PresheafOfModules) :
    SheafRestriction.Construction.moduleSheafificationUnit ((SheafRestriction.Construction.restrictModulePresheaf f).obj P) ≫
        (SheafRestriction.Construction.restrictSheafificationIso f P).hom.val =
      (SheafRestriction.Construction.restrictModulePresheaf f).map (SheafRestriction.Construction.moduleSheafificationUnit P) := by
  let := SheafRestriction.Construction.moduleSheafificationUnit_locallyInjective P
  let := SheafRestriction.Construction.moduleSheafificationUnit_locallySurjective P
  have hi := SheafRestriction.Construction.restrictModulePresheaf_locallyInjective f (SheafRestriction.Construction.moduleSheafificationUnit P)
  have hs := SheafRestriction.Construction.restrictModulePresheaf_locallySurjective f (SheafRestriction.Construction.moduleSheafificationUnit P)
  exact @moduleSheafificationUnit_isoOfLocallyBijective X _
    ((SheafTensor.Construction.sheafifyModule P).restrict f) _ hi hs

theorem sheafTensorHomEquiv_restrictTensorIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    SheafTensor.Construction.sheafTensorHomEquiv _ _ _ (TensorRestriction.Construction.restrictSheafTensorIso f M N).hom =
      (TensorRestriction.Construction.restrictPresheafTensorIso f M.val N.val).hom ≫
        (SheafRestriction.Construction.restrictModulePresheaf f).map (SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val)) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let L : X.PresheafOfModules ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv _ _
      (L.map (TensorRestriction.Construction.restrictPresheafTensorIso f M.val N.val).hom ≫
        (SheafRestriction.Construction.restrictSheafificationIso f (M.val ⊗ N.val)).hom) = _
  exact (adj.homEquiv_naturality_left (TensorRestriction.Construction.restrictPresheafTensorIso f M.val N.val).hom
    (SheafRestriction.Construction.restrictSheafificationIso f (M.val ⊗ N.val)).hom).trans
      (congrArg (fun q ↦ (TensorRestriction.Construction.restrictPresheafTensorIso f M.val N.val).hom ≫ q)
        ((adj.homEquiv_unit _ _ _).trans
          (moduleSheafificationUnit_restrictIso f (M.val ⊗ N.val))))

theorem restrictTensorIso_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (TensorFunctoriality.Construction.sheafTensorMap ((Scheme.Modules.restrictAdjunction f).unit.app M)
        ((Scheme.Modules.restrictAdjunction f).unit.app N) ≫
      TensorFunctoriality.Construction.pushforwardSheafTensorMap f (M.restrict f) (N.restrict f)) ≫
        (Scheme.Modules.pushforward f).map (TensorRestriction.Construction.restrictSheafTensorIso f M N).hom =
      (Scheme.Modules.restrictAdjunction f).unit.app (SheafTensor.Construction.sheafTensor M N) := by
  apply (SheafTensor.Construction.sheafTensorHomEquiv _ _ _).injective
  rw [TensorFunctoriality.Construction.sheafTensorHomEquiv_naturality_right, TensorFunctoriality.Construction.sheafTensorHomEquiv_naturality_left]
  dsimp only [Functor.comp_obj, Functor.id_obj, Scheme.Modules.restrict]
  simp only [TensorFunctoriality.Construction.pushforwardSheafTensorMap, Equiv.apply_symm_apply]
  let F := TensorFunctoriality.Construction.pushforwardModulePresheaf f
  let η := SheafRestriction.Construction.moduleSheafificationUnit ((M.restrict f).val ⊗ (N.restrict f).val)
  let ρ := (TensorRestriction.Construction.restrictSheafTensorIso f M N).hom.val
  let q := (TensorRestriction.Construction.restrictPresheafTensorIso f M.val N.val).hom ≫
    (SheafRestriction.Construction.restrictModulePresheaf f).map (SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val))
  have hρ : η ≫ ρ = q :=
    (TensorUnit.Construction.sheafTensorHomEquiv_apply_eq _).symm.trans (sheafTensorHomEquiv_restrictTensorIso f M N)
  have hF : F.map η ≫ F.map ρ = F.map q :=
    (F.map_comp η ρ).symm.trans (congrArg F.map hρ)
  rw [TensorUnit.Construction.sheafTensorHomEquiv_apply_eq]
  let t := ((Scheme.Modules.restrictAdjunction f).unit.app M).val ⊗ₘ
    ((Scheme.Modules.restrictAdjunction f).unit.app N).val
  let qf := TensorFunctoriality.Construction.pushforwardPresheafTensorMap f (M.restrict f).val (N.restrict f).val
  have hmain : t ≫ qf ≫ F.map q = SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val) ≫
      ((Scheme.Modules.restrictAdjunction f).unit.app (SheafTensor.Construction.sheafTensor M N)).val := by
    ext1 U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    have h := (SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val)).naturality
      (homOfLE (f.image_preimage_le U.unop)).op
    exact congrArg (fun a ↦ a (m ⊗ₜ[Γ(Y, U.unop)] n)) h
  change t ≫ (qf ≫ F.map η) ≫ F.map ρ = _
  exact (congrArg (fun a ↦ t ≫ a)
    ((Category.assoc qf (F.map η) (F.map ρ)).trans
      (congrArg (fun a ↦ qf ≫ a) hF))).trans hmain

theorem restrictFunctorIsoPullback_inv_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M) =
      (Scheme.Modules.restrictAdjunction f).unit.app M := by
  let R := Scheme.Modules.pushforward f
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have h : (Scheme.Modules.restrictAdjunction f).unit.app M ≫ R.map (e.hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  rw [← h, Category.assoc, ← R.map_comp, e.hom_inv_id_app, R.map_id]
  exact Category.comp_id _

theorem pullbackSheafTensorMap_restrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (TensorFunctoriality.Construction.pullbackSheafTensorMap f M N ≫
        TensorFunctoriality.Construction.sheafTensorMap ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M)
          ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app N)) ≫
        (TensorRestriction.Construction.restrictSheafTensorIso f M N).hom =
      (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (SheafTensor.Construction.sheafTensor M N) := by
  let L := Scheme.Modules.pullback f
  let R := Scheme.Modules.pushforward f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have hq :
      (TensorFunctoriality.Construction.sheafTensorMap (adj.unit.app M) (adj.unit.app N) ≫
        TensorFunctoriality.Construction.pushforwardSheafTensorMap f (L.obj M) (L.obj N)) ≫
        R.map (TensorFunctoriality.Construction.sheafTensorMap (e.inv.app M) (e.inv.app N)) =
      TensorFunctoriality.Construction.sheafTensorMap ((Scheme.Modules.restrictAdjunction f).unit.app M)
          ((Scheme.Modules.restrictAdjunction f).unit.app N) ≫
        TensorFunctoriality.Construction.pushforwardSheafTensorMap f (M.restrict f) (N.restrict f) := by
    rw [Category.assoc, TensorFunctoriality.Construction.pushforwardSheafTensorMap_naturality, ← Category.assoc,
      ← TensorFunctoriality.Construction.sheafTensorMap_comp, restrictFunctorIsoPullback_inv_unit,
      restrictFunctorIsoPullback_inv_unit]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right]
  simp only [TensorFunctoriality.Construction.pullbackSheafTensorMap, adj, Equiv.apply_symm_apply]
  change ((TensorFunctoriality.Construction.sheafTensorMap (adj.unit.app M) (adj.unit.app N) ≫
    TensorFunctoriality.Construction.pushforwardSheafTensorMap f (L.obj M) (L.obj N)) ≫
      R.map (TensorFunctoriality.Construction.sheafTensorMap (e.inv.app M) (e.inv.app N))) ≫
      R.map (TensorRestriction.Construction.restrictSheafTensorIso f M N).hom = adj.homEquiv _ _ (e.inv.app _)
  rw [hq, restrictTensorIso_unit, Adjunction.homEquiv_unit,
    restrictFunctorIsoPullback_inv_unit]
  rfl

theorem isIso_pullbackSheafTensorMap_of_openImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f M N) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have : IsIso (TensorFunctoriality.Construction.sheafTensorMap (e.inv.app M) (e.inv.app N)) := TensorUnit.Construction.sheafTensorMap_isIso _ _
  have : IsIso ((TensorFunctoriality.Construction.pullbackSheafTensorMap f M N ≫
      TensorFunctoriality.Construction.sheafTensorMap (e.inv.app M) (e.inv.app N)) ≫ (TensorRestriction.Construction.restrictSheafTensorIso f M N).hom) := by
    rw [pullbackSheafTensorMap_restrict]
    infer_instance
  have : IsIso (TensorFunctoriality.Construction.pullbackSheafTensorMap f M N ≫ TensorFunctoriality.Construction.sheafTensorMap (e.inv.app M) (e.inv.app N)) :=
    IsIso.of_isIso_comp_right _ (TensorRestriction.Construction.restrictSheafTensorIso f M N).hom
  exact IsIso.of_isIso_comp_right _ (TensorFunctoriality.Construction.sheafTensorMap (e.inv.app M) (e.inv.app N))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorOpenComparison.Construction

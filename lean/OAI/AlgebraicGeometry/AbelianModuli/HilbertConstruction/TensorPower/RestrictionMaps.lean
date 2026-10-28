import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps

/-! # Restriction Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps

noncomputable section

/-! Canonical restriction comparison for tensor powers, compatible with maps of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  (L : Y.Modules) (n : ℕ)

/-- The restricted tensor-power sheaf has the universal multilinear correspondence. -/
def tensorPowerRestrictHomEquiv (P : X.Modules) :
    ((PowerSheaf.tensorPowerModule L n).restrict f ⟶ P) ≃ Tensor.Powers.SheafMultilinearMap (L.restrict f) n P :=
  ((Scheme.Modules.restrictAdjunction f).homEquiv (PowerSheaf.tensorPowerModule L n) P).trans
    ((PowerSheaf.tensorPowerHomEquiv L ((Scheme.Modules.pushforward f).obj P) n).trans
      (Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n P).symm)

theorem tensorPowerRestrictMultilinear_postcomp {P : X.Modules}
    (h : (PowerSheaf.tensorPowerModule L n).restrict f ⟶ P) :
    ((Maps.tensorPowerMultilinear L n).restrict f).postcomp h =
      tensorPowerRestrictHomEquiv f L n P h := by
  apply (Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n P).injective
  exact (Tensor.Powers.SheafMultilinearMap.restrictHomEquiv_postcomp _ f h).trans
    ((Maps.tensorPowerMultilinear_postcomp _).trans
      ((Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n P).apply_symm_apply _).symm)

theorem tensorPowerRestrict_hom_ext {P : X.Modules}
    {a b : (PowerSheaf.tensorPowerModule L n).restrict f ⟶ P}
    (h : ((Maps.tensorPowerMultilinear L n).restrict f).postcomp a =
      ((Maps.tensorPowerMultilinear L n).restrict f).postcomp b) : a = b :=
  (tensorPowerRestrictHomEquiv f L n P).injective
    ((tensorPowerRestrictMultilinear_postcomp f L n a).symm.trans
      (h.trans (tensorPowerRestrictMultilinear_postcomp f L n b)))

/-- The canonical comparison from the power of the restriction to the restricted power. -/
def tensorPowerRestrictHom : PowerSheaf.tensorPowerModule (L.restrict f) n ⟶ (PowerSheaf.tensorPowerModule L n).restrict f :=
  (PowerSheaf.tensorPowerHomEquiv (L.restrict f) ((PowerSheaf.tensorPowerModule L n).restrict f) n).symm
    ((Maps.tensorPowerMultilinear L n).restrict f)

/-- The inverse comparison, obtained from the restricted universal property. -/
def tensorPowerRestrictInv : (PowerSheaf.tensorPowerModule L n).restrict f ⟶ PowerSheaf.tensorPowerModule (L.restrict f) n :=
  (tensorPowerRestrictHomEquiv f L n (PowerSheaf.tensorPowerModule (L.restrict f) n)).symm
    (Maps.tensorPowerMultilinear (L.restrict f) n)

theorem tensorPowerRestrictHom_spec :
    (Maps.tensorPowerMultilinear (L.restrict f) n).postcomp (tensorPowerRestrictHom f L n) =
      (Maps.tensorPowerMultilinear L n).restrict f :=
  (Maps.tensorPowerMultilinear_postcomp _).trans
    ((PowerSheaf.tensorPowerHomEquiv (L.restrict f) ((PowerSheaf.tensorPowerModule L n).restrict f) n).apply_symm_apply _)

theorem tensorPowerRestrictInv_spec :
    ((Maps.tensorPowerMultilinear L n).restrict f).postcomp (tensorPowerRestrictInv f L n) =
      Maps.tensorPowerMultilinear (L.restrict f) n :=
  (tensorPowerRestrictMultilinear_postcomp f L n _).trans
    ((tensorPowerRestrictHomEquiv f L n (PowerSheaf.tensorPowerModule (L.restrict f) n)).apply_symm_apply _)

/-- Tensor powers commute canonically with restriction to an open subscheme. -/
def tensorPowerRestrictIso : PowerSheaf.tensorPowerModule (L.restrict f) n ≅ (PowerSheaf.tensorPowerModule L n).restrict f where
  hom := tensorPowerRestrictHom f L n
  inv := tensorPowerRestrictInv f L n
  hom_inv_id := by
    apply Maps.tensorPower_hom_ext
    exact (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).trans
      ((congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) n ((PowerSheaf.tensorPowerModule L n).restrict f) =>
        β.postcomp (tensorPowerRestrictInv f L n)) (tensorPowerRestrictHom_spec f L n)).trans
          ((tensorPowerRestrictInv_spec f L n).trans (Tensor.Powers.SheafMultilinearMap.postcomp_id _).symm))
  inv_hom_id := by
    apply tensorPowerRestrict_hom_ext f L n
    exact (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).trans
      ((congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) n (PowerSheaf.tensorPowerModule (L.restrict f) n) =>
        β.postcomp (tensorPowerRestrictHom f L n)) (tensorPowerRestrictInv_spec f L n)).trans
          ((tensorPowerRestrictHom_spec f L n).trans (Tensor.Powers.SheafMultilinearMap.postcomp_id _).symm))

variable {L n}

/-- The canonical restriction comparison commutes with maps of all tensor factors. -/
theorem tensorPowerRestrictIso_naturality {M : Y.Modules} (a : L ⟶ M) :
    Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n ≫ (tensorPowerRestrictIso f M n).hom =
      (tensorPowerRestrictIso f L n).hom ≫ (Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n) := by
  apply Maps.tensorPower_hom_ext
  calc
    (Maps.tensorPowerMultilinear (L.restrict f) n).postcomp
        (Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n ≫
          (tensorPowerRestrictIso f M n).hom) =
      ((Maps.tensorPowerMultilinear (L.restrict f) n).postcomp
        (Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n)).postcomp
          (tensorPowerRestrictIso f M n).hom := Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _
    _ = ((Maps.tensorPowerMultilinear (M.restrict f) n).precomp
        ((Scheme.Modules.restrictFunctor f).map a)).postcomp (tensorPowerRestrictIso f M n).hom :=
      congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) n (PowerSheaf.tensorPowerModule (M.restrict f) n) =>
        β.postcomp (tensorPowerRestrictIso f M n).hom) (Maps.tensorPowerMap_spec _ _)
    _ = ((Maps.tensorPowerMultilinear M n).restrict f).precomp ((Scheme.Modules.restrictFunctor f).map a) :=
      (Tensor.Powers.SheafMultilinearMap.precomp_postcomp _ _ _).symm.trans
        (congrArg (fun β : Tensor.Powers.SheafMultilinearMap (M.restrict f) n ((PowerSheaf.tensorPowerModule M n).restrict f) =>
          β.precomp ((Scheme.Modules.restrictFunctor f).map a)) (tensorPowerRestrictHom_spec f M n))
    _ = ((Maps.tensorPowerMultilinear M n).precomp a).restrict f :=
      (Tensor.Powers.SheafMultilinearMap.restrict_precomp _ f a).symm
    _ = ((Maps.tensorPowerMultilinear L n).postcomp (Maps.tensorPowerMap a n)).restrict f :=
      congrArg (fun β : Tensor.Powers.SheafMultilinearMap L n (PowerSheaf.tensorPowerModule M n) => β.restrict f)
        (Maps.tensorPowerMap_spec a n).symm
    _ = ((Maps.tensorPowerMultilinear L n).restrict f).postcomp
        ((Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)) :=
      Tensor.Powers.SheafMultilinearMap.restrict_postcomp _ f _
    _ = (Maps.tensorPowerMultilinear (L.restrict f) n).postcomp
        ((tensorPowerRestrictIso f L n).hom ≫ (Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)) :=
      (congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) n ((PowerSheaf.tensorPowerModule L n).restrict f) =>
        β.postcomp ((Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)))
          (tensorPowerRestrictHom_spec f L n).symm).trans
            (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).symm

/-- A map that is invertible on an open stays invertible there after taking tensor powers. -/
theorem tensorPowerMap_restrict_isIso {M : Y.Modules} (a : L ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor f).map a)] :
    IsIso ((Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)) := by
  have : IsIso (Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n) :=
    (Maps.tensorPowerFunctor X n).map_isIso _
  have he := tensorPowerRestrictIso_naturality (n := n) f a
  have : IsIso ((tensorPowerRestrictIso f L n).hom ≫
      (Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp this

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps

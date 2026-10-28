import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultilinearComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Single and iterated tensor powers of a line bundle are canonically isomorphic. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {X Y : Scheme.{u}} {L M : X.Modules}

/-- Multiplication in the structure sheaf is compatible with grouping tensor factors. -/
theorem Iterated.Powers.structureModuleTensorMap_compose (X : Scheme.{u}) (m n : ℕ) :
    (LineBundle.Powers.structureModuleTensorMap X m).compose (LineBundle.Powers.structureModuleTensorMap X n) =
      LineBundle.Powers.structureModuleTensorMap X (m * n) := by
  apply Tensor.Powers.SheafMultilinearMap.ext
  intro U
  apply MultilinearMap.ext_ring
  change (∏ _ : Fin m, (∏ _ : Fin n, (1 : Γ(X, U)))) = ∏ _ : Fin (m * n), (1 : Γ(X, U))
  simp only [Finset.prod_const_one]

/-- The canonical trivialization of an iterated power of the structure module. -/
def Iterated.Powers.tensorPowerIteratedUnitIso (X : Scheme.{u}) (m n : ℕ) :
    TensorPower.PowerSheaf.tensorPowerModule (TensorPower.PowerSheaf.tensorPowerModule (Line.Bundles.structureModule X) n) m ≅ Line.Bundles.structureModule X :=
  (TensorPower.Maps.tensorPowerFunctor X m).mapIso (TensorPower.Maps.tensorPowerUnitIso X n) ≪≫ TensorPower.Maps.tensorPowerUnitIso X m

theorem Iterated.Powers.tensorPowerComposeMap_unit (X : Scheme.{u}) (m n : ℕ) :
    MultilinearComposition.tensorPowerComposeMap (Line.Bundles.structureModule X) m n ≫ (Iterated.Powers.tensorPowerIteratedUnitIso X m n).hom =
      (TensorPower.Maps.tensorPowerUnitIso X (m * n)).hom := by
  apply TensorPower.Maps.tensorPower_hom_ext
  change (TensorPower.Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) (m * n)).postcomp
    (MultilinearComposition.tensorPowerComposeMap (Line.Bundles.structureModule X) m n ≫
      TensorPower.Maps.tensorPowerMap (TensorPower.Maps.tensorPowerUnitHom X n) m ≫ TensorPower.Maps.tensorPowerUnitHom X m) = _
  rw [Tensor.Powers.SheafMultilinearMap.postcomp_comp, MultilinearComposition.tensorPowerComposeMap_spec,
    Tensor.Powers.SheafMultilinearMap.postcomp_comp, Tensor.Powers.SheafMultilinearMap.compose_postcomp,
    TensorPower.Maps.tensorPowerMap_spec, Tensor.Powers.SheafMultilinearMap.compose_middle, TensorPower.Maps.tensorPowerUnitHom_spec,
    Tensor.Powers.SheafMultilinearMap.compose_postcomp, TensorPower.Maps.tensorPowerUnitHom_spec,
    Iterated.Powers.structureModuleTensorMap_compose]
  exact (TensorPower.Maps.tensorPowerUnitHom_spec X (m * n)).symm

instance Iterated.Powers.tensorPowerComposeMap_unit_isIso (X : Scheme.{u}) (m n : ℕ) :
    IsIso (MultilinearComposition.tensorPowerComposeMap (Line.Bundles.structureModule X) m n) := by
  have : IsIso (MultilinearComposition.tensorPowerComposeMap (Line.Bundles.structureModule X) m n ≫
      (Iterated.Powers.tensorPowerIteratedUnitIso X m n).hom) :=
    (Iterated.Powers.tensorPowerComposeMap_unit X m n).symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

/-- A globally trivialized line bundle has the expected iterated-power comparison. -/
theorem Iterated.Powers.tensorPowerComposeMap_isIso_of_frame (e : L ≅ Line.Bundles.structureModule X) (m n : ℕ) :
    IsIso (MultilinearComposition.tensorPowerComposeMap L m n) := by
  have : IsIso (TensorPower.Maps.tensorPowerMap e.hom (m * n)) := (TensorPower.Maps.tensorPowerFunctor X (m * n)).map_isIso _
  have : IsIso (TensorPower.Maps.tensorPowerMap e.hom n) := (TensorPower.Maps.tensorPowerFunctor X n).map_isIso _
  have : IsIso (TensorPower.Maps.tensorPowerMap (TensorPower.Maps.tensorPowerMap e.hom n) m) := (TensorPower.Maps.tensorPowerFunctor X m).map_isIso _
  have he := MultilinearComposition.tensorPowerComposeMap_naturality e.hom m n
  have : IsIso (MultilinearComposition.tensorPowerComposeMap L m n ≫ TensorPower.Maps.tensorPowerMap (TensorPower.Maps.tensorPowerMap e.hom n) m) :=
    he ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

/-- Restriction preserves substitution of multilinear sheaf maps. -/
theorem Tensor.Powers.SheafMultilinearMap.compose_restrict {L M P : Y.Modules} {m n : ℕ}
    (γ : Tensor.Powers.SheafMultilinearMap M m P) (β : Tensor.Powers.SheafMultilinearMap L n M)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (γ.compose β).restrict f = (γ.restrict f).compose (β.restrict f) := by
  ext U s
  rfl

/-- Apply the canonical restriction comparisons to both powers in an iterated power. -/
def Iterated.Powers.tensorPowerIteratedRestrictIso (f : X ⟶ Y) [IsOpenImmersion f] (L : Y.Modules) (m n : ℕ) :
    TensorPower.PowerSheaf.tensorPowerModule (TensorPower.PowerSheaf.tensorPowerModule (L.restrict f) n) m ≅
      (TensorPower.PowerSheaf.tensorPowerModule (TensorPower.PowerSheaf.tensorPowerModule L n) m).restrict f :=
  (TensorPower.Maps.tensorPowerFunctor X m).mapIso (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n) ≪≫
    TensorPower.RestrictionMaps.tensorPowerRestrictIso f (TensorPower.PowerSheaf.tensorPowerModule L n) m

/-- The single-to-iterated comparison commutes with restriction to any open subscheme. -/
theorem Iterated.Powers.tensorPowerComposeMap_restrict (f : X ⟶ Y) [IsOpenImmersion f]
    (L : Y.Modules) (m n : ℕ) :
    MultilinearComposition.tensorPowerComposeMap (L.restrict f) m n ≫ (Iterated.Powers.tensorPowerIteratedRestrictIso f L m n).hom =
      (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L (m * n)).hom ≫
        (Scheme.Modules.restrictFunctor f).map (MultilinearComposition.tensorPowerComposeMap L m n) := by
  apply TensorPower.Maps.tensorPower_hom_ext
  change (TensorPower.Maps.tensorPowerMultilinear (L.restrict f) (m * n)).postcomp
    (MultilinearComposition.tensorPowerComposeMap (L.restrict f) m n ≫
      TensorPower.Maps.tensorPowerMap (TensorPower.RestrictionMaps.tensorPowerRestrictHom f L n) m ≫
        TensorPower.RestrictionMaps.tensorPowerRestrictHom f (TensorPower.PowerSheaf.tensorPowerModule L n) m) = _
  rw [Tensor.Powers.SheafMultilinearMap.postcomp_comp, MultilinearComposition.tensorPowerComposeMap_spec,
    Tensor.Powers.SheafMultilinearMap.postcomp_comp, Tensor.Powers.SheafMultilinearMap.compose_postcomp,
    TensorPower.Maps.tensorPowerMap_spec, Tensor.Powers.SheafMultilinearMap.compose_middle, TensorPower.RestrictionMaps.tensorPowerRestrictHom_spec,
    Tensor.Powers.SheafMultilinearMap.compose_postcomp, TensorPower.RestrictionMaps.tensorPowerRestrictHom_spec,
    ← Tensor.Powers.SheafMultilinearMap.compose_restrict,
    ← MultilinearComposition.tensorPowerComposeMap_spec, Tensor.Powers.SheafMultilinearMap.restrict_postcomp]
  exact (congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) (m * n)
      ((TensorPower.PowerSheaf.tensorPowerModule L (m * n)).restrict f) =>
        β.postcomp ((Scheme.Modules.restrictFunctor f).map (MultilinearComposition.tensorPowerComposeMap L m n)))
      (TensorPower.RestrictionMaps.tensorPowerRestrictHom_spec f L (m * n)).symm).trans
        (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).symm

/-- The iterated-power comparison is invertible for every algebraic line bundle. -/
instance Line.Bundles.LineBundle.tensorPowerComposeMap_isIso (L : Line.Bundles.LineBundle X) (m n : ℕ) :
    IsIso (MultilinearComposition.tensorPowerComposeMap L.sheaf m n) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  refine ⟨U, hx, ?_⟩
  have : IsIso (MultilinearComposition.tensorPowerComposeMap (L.sheaf.restrict U.ι) m n) :=
    Iterated.Powers.tensorPowerComposeMap_isIso_of_frame
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf ≪≫ e) m n
  have he := Iterated.Powers.tensorPowerComposeMap_restrict U.ι L.sheaf m n
  have hi : IsIso ((TensorPower.RestrictionMaps.tensorPowerRestrictIso U.ι L.sheaf (m * n)).hom ≫
      (Scheme.Modules.restrictFunctor U.ι).map (MultilinearComposition.tensorPowerComposeMap L.sheaf m n)) := he ▸ inferInstance
  exact (Power.Nonvanishing.isIso_restrict_map_iff U.ι _).mp ((isIso_comp_left_iff _ _).mp hi)

/-- The power of degree m*n is canonically the mth power of the nth power. -/
def Line.Bundles.LineBundle.tensorPowerComposeIso (L : Line.Bundles.LineBundle X) (m n : ℕ) :
    (L.tensorPower (m * n)).sheaf ≅ ((L.tensorPower n).tensorPower m).sheaf := by
  exact @asIso X.Modules _ _ _ (MultilinearComposition.tensorPowerComposeMap L.sheaf m n)
    (L.tensorPowerComposeMap_isIso m n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

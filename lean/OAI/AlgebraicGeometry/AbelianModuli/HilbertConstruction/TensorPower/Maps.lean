import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers

/-! # Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps

noncomputable section

/-! Functorial tensor powers of module sheaves and powers of actual line-bundle sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M P Q : X.Modules} {n : ℕ}

/-- The canonical multilinear map into the constructed tensor-power sheaf. -/
def tensorPowerMultilinear (L : X.Modules) (n : ℕ) :
    Tensor.Powers.SheafMultilinearMap L n (PowerSheaf.tensorPowerModule L n) :=
  PowerSheaf.tensorPowerHomEquiv L (PowerSheaf.tensorPowerModule L n) n (𝟙 _)

theorem tensorPowerMultilinear_postcomp (f : PowerSheaf.tensorPowerModule L n ⟶ P) :
    (tensorPowerMultilinear L n).postcomp f = PowerSheaf.tensorPowerHomEquiv L P n f :=
  (PowerSheaf.tensorPowerHomEquiv_postcomp (𝟙 _) f).symm.trans
    (congrArg (PowerSheaf.tensorPowerHomEquiv L P n) (Category.id_comp f))

/-- The canonical multilinear map detects equality of maps out of the tensor power. -/
theorem tensorPower_hom_ext {f h : PowerSheaf.tensorPowerModule L n ⟶ P}
    (he : (tensorPowerMultilinear L n).postcomp f = (tensorPowerMultilinear L n).postcomp h) :
    f = h :=
  (PowerSheaf.tensorPowerHomEquiv L P n).injective
    ((tensorPowerMultilinear_postcomp f).symm.trans
      (he.trans (tensorPowerMultilinear_postcomp h)))

/-- Apply the same module-sheaf morphism to every tensor factor. -/
def tensorPowerMap (f : L ⟶ M) (n : ℕ) : PowerSheaf.tensorPowerModule L n ⟶ PowerSheaf.tensorPowerModule M n :=
  (PowerSheaf.tensorPowerHomEquiv L (PowerSheaf.tensorPowerModule M n) n).symm
    ((tensorPowerMultilinear M n).precomp f)

theorem tensorPowerMap_spec (f : L ⟶ M) (n : ℕ) :
    (tensorPowerMultilinear L n).postcomp (tensorPowerMap f n) =
      (tensorPowerMultilinear M n).precomp f :=
  (tensorPowerMultilinear_postcomp _).trans
    ((PowerSheaf.tensorPowerHomEquiv L (PowerSheaf.tensorPowerModule M n) n).apply_symm_apply _)

@[simp]
theorem tensorPowerMap_id (L : X.Modules) (n : ℕ) : tensorPowerMap (𝟙 L) n = 𝟙 _ := by
  apply tensorPower_hom_ext
  exact (tensorPowerMap_spec (𝟙 L) n).trans
    ((Tensor.Powers.SheafMultilinearMap.precomp_id _).trans (Tensor.Powers.SheafMultilinearMap.postcomp_id _).symm)

theorem tensorPowerMap_comp (f : L ⟶ M) (h : M ⟶ P) (n : ℕ) :
    tensorPowerMap (f ≫ h) n = tensorPowerMap f n ≫ tensorPowerMap h n := by
  apply tensorPower_hom_ext
  calc
    (tensorPowerMultilinear L n).postcomp (tensorPowerMap (f ≫ h) n) =
        (tensorPowerMultilinear P n).precomp (f ≫ h) := tensorPowerMap_spec _ _
    _ = ((tensorPowerMultilinear P n).precomp h).precomp f :=
      (Tensor.Powers.SheafMultilinearMap.precomp_comp _ h f).symm
    _ = ((tensorPowerMultilinear M n).postcomp (tensorPowerMap h n)).precomp f :=
      congrArg (fun β : Tensor.Powers.SheafMultilinearMap M n (PowerSheaf.tensorPowerModule P n) => β.precomp f)
        (tensorPowerMap_spec h n).symm
    _ = ((tensorPowerMultilinear M n).precomp f).postcomp (tensorPowerMap h n) :=
      Tensor.Powers.SheafMultilinearMap.precomp_postcomp _ _ _
    _ = ((tensorPowerMultilinear L n).postcomp (tensorPowerMap f n)).postcomp
        (tensorPowerMap h n) :=
      congrArg (fun β : Tensor.Powers.SheafMultilinearMap L n (PowerSheaf.tensorPowerModule M n) =>
        β.postcomp (tensorPowerMap h n)) (tensorPowerMap_spec f n).symm
    _ = (tensorPowerMultilinear L n).postcomp (tensorPowerMap f n ≫ tensorPowerMap h n) :=
      (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).symm

/-- Tensor powers form a functor on the actual category of module sheaves. -/
def tensorPowerFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ X.Modules where
  obj L := PowerSheaf.tensorPowerModule L n
  map f := tensorPowerMap f n
  map_id L := tensorPowerMap_id L n
  map_comp f h := tensorPowerMap_comp f h n

/-- A map from a tensor power of the unit to the unit is multiplication of its factors. -/
def tensorPowerUnitHom (X : Scheme.{u}) (n : ℕ) :
    PowerSheaf.tensorPowerModule (Line.Bundles.structureModule X) n ⟶ Line.Bundles.structureModule X :=
  (PowerSheaf.tensorPowerHomEquiv (Line.Bundles.structureModule X) (Line.Bundles.structureModule X) n).symm
    (LineBundle.Powers.structureModuleTensorMap X n)

/-- The inverse map is determined by the value of the universal tensor on ones. -/
def tensorPowerUnitInv (X : Scheme.{u}) (n : ℕ) :
    Line.Bundles.structureModule X ⟶ PowerSheaf.tensorPowerModule (Line.Bundles.structureModule X) n :=
  (tensorPowerMultilinear (Line.Bundles.structureModule X) n).unitToHom

theorem tensorPowerUnitHom_spec (X : Scheme.{u}) (n : ℕ) :
    (tensorPowerMultilinear (Line.Bundles.structureModule X) n).postcomp (tensorPowerUnitHom X n) =
      LineBundle.Powers.structureModuleTensorMap X n :=
  (tensorPowerMultilinear_postcomp _).trans
    ((PowerSheaf.tensorPowerHomEquiv (Line.Bundles.structureModule X) (Line.Bundles.structureModule X) n).apply_symm_apply _)

/-- The canonical tensor power of the structure sheaf is canonically the structure sheaf. -/
def tensorPowerUnitIso (X : Scheme.{u}) (n : ℕ) :
    PowerSheaf.tensorPowerModule (Line.Bundles.structureModule X) n ≅ Line.Bundles.structureModule X where
  hom := tensorPowerUnitHom X n
  inv := tensorPowerUnitInv X n
  hom_inv_id := by
    apply tensorPower_hom_ext
    exact (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).trans
      ((congrArg (fun β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n (Line.Bundles.structureModule X) =>
        β.postcomp (tensorPowerUnitInv X n)) (tensorPowerUnitHom_spec X n)).trans
          ((LineBundle.Powers.structureModuleTensorMap_postcomp_unitToHom _).trans
            (Tensor.Powers.SheafMultilinearMap.postcomp_id _).symm))
  inv_hom_id := by
    have h := congrArg Tensor.Powers.SheafMultilinearMap.unitToHom (tensorPowerUnitHom_spec X n)
    have he : ((tensorPowerMultilinear (Line.Bundles.structureModule X) n).postcomp
        (tensorPowerUnitHom X n)).unitToHom = tensorPowerUnitInv X n ≫ tensorPowerUnitHom X n := by
      apply Scheme.Modules.hom_ext
      intro U
      apply ConcreteCategory.hom_ext
      intro r
      exact ((tensorPowerUnitHom X n).app_smul r
        ((tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U
          (fun _ => (1 : Γ(X, U))))).symm
    exact he.symm.trans (h.trans (by
      simpa only [Tensor.Powers.SheafMultilinearMap.postcomp_id] using
        (LineBundle.Powers.unitToHom_structureModuleTensorMap_postcomp (X := X) (n := n) (𝟙 (Line.Bundles.structureModule X)))))

/-- Raising a section to a power, as a morphism into the tensor-power sheaf. -/
def tensorPowerSection (s : Line.Bundles.structureModule X ⟶ L) (n : ℕ) :
    Line.Bundles.structureModule X ⟶ PowerSheaf.tensorPowerModule L n :=
  (tensorPowerUnitIso X n).inv ≫ tensorPowerMap s n

/-- On sections, the power of a section is the universal tensor of its repeated value. -/
theorem tensorPowerSection_app (s : Line.Bundles.structureModule X ⟶ L) (n : ℕ) (U : X.Opens)
    (r : Γ(X, U)) :
    (tensorPowerSection s n).app U r =
      r • (tensorPowerMultilinear L n).app U (fun _ => s.app U (1 : Γ(X, U))) := by
  have hs := congrArg (fun β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n (PowerSheaf.tensorPowerModule L n) =>
    β.app U (fun _ => (1 : Γ(X, U)))) (tensorPowerMap_spec s n)
  change (tensorPowerMap s n).app U
      ((tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U (fun _ => (1 : Γ(X, U)))) =
    (tensorPowerMultilinear L n).app U (fun _ => s.app U (1 : Γ(X, U))) at hs
  exact ((tensorPowerMap s n).app_smul r _).trans
    (congrArg (fun a : Γ(PowerSheaf.tensorPowerModule L n, U) => r • a) hs)

/-- A global frame raises to a global frame in every tensor power. -/
instance tensorPowerSection_isIso (s : Line.Bundles.structureModule X ⟶ L) [IsIso s] (n : ℕ) :
    IsIso (tensorPowerSection s n) := by
  have : IsIso (tensorPowerMap s n) := (tensorPowerFunctor X n).map_isIso s
  dsimp [tensorPowerSection]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps

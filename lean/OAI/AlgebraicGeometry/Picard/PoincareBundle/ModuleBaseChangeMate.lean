import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Module Base Change Mate -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeMate

noncomputable section

/-!
# The canonical affine base-change mate for PoincareBundle

The tensor base-change isomorphism is identified with the actual mate
of the commutative square of restriction-of-scalars functors.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

/-- Component formula for the inverse mates correspondence. -/
theorem inverseMate_app {C D E F : Type*} [Category* C] [Category* D]
    [Category* E] [Category* F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (γ : TwoSquare R₁ H G R₂) (M : C) :
    ((mateEquiv adj₁ adj₂).symm γ).app M =
      L₂.map (G.map (adj₁.unit.app M)) ≫ L₂.map (γ.app (L₁.obj M)) ≫
        adj₂.counit.app (H.obj (L₁.obj M)) := by
  dsimp [mateEquiv]
  simp

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- The map from the second algebra to the tensor ring. -/
abbrev rightMap : T →+* S ⊗[R] T :=
  (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom

/-- The two maps from the base ring to the tensor ring agree. -/
theorem square_commutes :
    (algebraMap S (S ⊗[R] T)).comp (algebraMap R S) =
      (rightMap R S T).comp (algebraMap R T) := by
  ext r
  exact ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes r).trans
    ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes r).symm

/-- Restricting through either side of the tensor-ring square agrees. -/
def restrictionSquareIso :
    ModuleCat.restrictScalars (algebraMap S (S ⊗[R] T)) ⋙
        ModuleCat.restrictScalars (algebraMap R S) ≅
      ModuleCat.restrictScalars (rightMap R S T) ⋙ ModuleCat.restrictScalars (algebraMap R T) :=
  (ModuleCat.restrictScalarsComp (algebraMap R S) (algebraMap S (S ⊗[R] T))).symm ≪≫
    ModuleCat.restrictScalarsComp' (algebraMap R T) (rightMap R S T)
      ((algebraMap S (S ⊗[R] T)).comp (algebraMap R S)) (square_commutes R S T)

/-- The restriction-square comparison acts identically on the original module. -/
theorem restrictionSquareIso_hom_apply (M : ModuleCat.{u} (S ⊗[R] T)) (m : M) :
    (restrictionSquareIso R S T).hom.app M m = m := rfl

/-- The canonical adjunction base-change map. -/
def baseChangeMap : ModuleBaseChangeFunctor.sourceFunctor R S T ⟶
    ModuleBaseChangeFunctor.targetFunctor R S T :=
  ((mateEquiv (ModuleCat.extendRestrictScalarsAdj (algebraMap S (S ⊗[R] T)))
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R T))).symm
      (TwoSquare.mk _ _ _ _ (restrictionSquareIso R S T).hom)).natTrans

/-- The mate is the composite of the actual unit, restriction comparison, and counit. -/
theorem baseChangeMap_app (M : ModuleCat.{u} S) :
    (baseChangeMap R S T).app M =
      (ModuleCat.extendScalars (algebraMap R T)).map
        ((ModuleCat.restrictScalars (algebraMap R S)).map
          ((ModuleCat.extendRestrictScalarsAdj (algebraMap S (S ⊗[R] T))).unit.app M)) ≫
      (ModuleCat.extendScalars (algebraMap R T)).map
        ((restrictionSquareIso R S T).hom.app
          ((ModuleCat.extendScalars (algebraMap S (S ⊗[R] T))).obj M)) ≫
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R T)).counit.app
        ((ModuleCat.restrictScalars (rightMap R S T)).obj
          ((ModuleCat.extendScalars (algebraMap S (S ⊗[R] T))).obj M)) := by
  exact inverseMate_app
    (ModuleCat.extendRestrictScalarsAdj (algebraMap S (S ⊗[R] T)))
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R T))
    (TwoSquare.mk _ _ _ _ (restrictionSquareIso R S T).hom) M

/-- The extension unit, viewed through the commutative restriction square. -/
def liftedUnit (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj M ⟶
      (ModuleCat.restrictScalars (algebraMap R T)).obj
        ((ModuleCat.restrictScalars (rightMap R S T)).obj
          ((ModuleCat.extendScalars (algebraMap S (S ⊗[R] T))).obj M)) :=
  (ModuleCat.restrictScalars (algebraMap R S)).map
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap S (S ⊗[R] T))).unit.app M) ≫
    (restrictionSquareIso R S T).hom.app
      ((ModuleCat.extendScalars (algebraMap S (S ⊗[R] T))).obj M)

/-- Its underlying formula is the unit pure tensor. -/
theorem liftedUnit_apply (M : ModuleCat.{u} S)
    (m : (ModuleCat.restrictScalars (algebraMap R S)).obj M) :
    liftedUnit R S T M m =
      (1 : S ⊗[R] T) ⊗ₜ[S,algebraMap S (S ⊗[R] T)] (show M from m) := rfl

/-- The canonical mate is the adjoint transpose of the lifted unit. -/
theorem baseChangeMap_app_liftedUnit (M : ModuleCat.{u} S) :
    (baseChangeMap R S T).app M =
      (ModuleCat.extendScalars (algebraMap R T)).map (liftedUnit R S T M) ≫
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R T)).counit.app
          ((ModuleCat.restrictScalars (rightMap R S T)).obj
            ((ModuleCat.extendScalars (algebraMap S (S ⊗[R] T))).obj M)) := by
  let a := (ModuleCat.restrictScalars (algebraMap R S)).map
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap S (S ⊗[R] T))).unit.app M)
  let b := (restrictionSquareIso R S T).hom.app
    ((ModuleCat.extendScalars (algebraMap S (S ⊗[R] T))).obj M)
  let c := (ModuleCat.extendRestrictScalarsAdj (algebraMap R T)).counit.app
    ((ModuleCat.restrictScalars (rightMap R S T)).obj
      ((ModuleCat.extendScalars (algebraMap S (S ⊗[R] T))).obj M))
  let L := ModuleCat.extendScalars (algebraMap R T)
  exact (baseChangeMap_app R S T M).trans
    ((Category.assoc (L.map a) (L.map b) c).symm.trans
      (congrArg (fun k => k ≫ c) (L.map_comp a b).symm))

/-- The canonical mate sends the unit pure tensor to the unit extended tensor. -/
theorem baseChangeMap_one_tmul (M : ModuleCat.{u} S)
    (m : (ModuleCat.restrictScalars (algebraMap R S)).obj M) :
    (baseChangeMap R S T).app M ((1 : T) ⊗ₜ[R,algebraMap R T] m) =
      (1 : S ⊗[R] T) ⊗ₜ[S,algebraMap S (S ⊗[R] T)] (show M from m) := by
  erw [baseChangeMap_app_liftedUnit, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  erw [ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul, liftedUnit_apply]

/-- The affine base-change mate is exactly the proved tensor isomorphism. -/
theorem baseChangeMap_eq :
    baseChangeMap R S T = (ModuleBaseChangeFunctor.baseChangeIso R S T).hom := by
  apply NatTrans.ext
  funext M
  apply ModuleCat.ExtendScalars.hom_ext (f := algebraMap R T)
  intro m
  erw [baseChangeMap_one_tmul]
  exact (ModuleBaseChangeFunctor.objectIso_hom_tmul R S T M 1 m).symm

/-- The canonical affine base-change map is invertible. -/
theorem baseChangeMap_isIso : IsIso (baseChangeMap R S T) := by
  rw [baseChangeMap_eq]
  infer_instance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeMate

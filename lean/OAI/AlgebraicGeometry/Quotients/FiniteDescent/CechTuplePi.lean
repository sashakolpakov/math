import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechProducts
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Cech Tuple Pi -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTuplePi

noncomputable section

/-! Coordinate changes from tuples to the first three ordinary Cech terms. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechTupleCoordinates

def indexZero (ι : Type u) : (Fin 1 → ι) ≃ ι where
  toFun a := a 0
  invFun i := fun _ => i
  left_inv a := by funext k; exact congrArg a (Subsingleton.elim _ _)
  right_inv _ := rfl

def indexTwo (ι : Type u) : (Fin 3 → ι) ≃ ι × (ι × ι) where
  toFun a := (a 0, a 1, a 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv a := by funext k; fin_cases k <;> rfl
  right_inv _ := rfl

def reindex {R : Type u} [CommRing R] {X : Scheme.{u}}
    (F : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) {I J : Type u}
    (V : I → X.Opens) (W : J → X.Opens) (e : I ≃ J)
    (he : ∀ j, V (e.symm j) = W j) :
    (∀ i, F.obj (op (V i))) ≃ₗ[R] (∀ j, F.obj (op (W j))) :=
  (LinearEquiv.piCongrLeft' R (fun i => F.obj (op (V i))) e).trans
    (LinearEquiv.piCongrRight fun j => (F.mapIso (eqToIso (he j).symm).op).toLinearEquiv)

def curry {R : Type u} [CommRing R] {I J : Type u}
    (A : I → J → ModuleCat.{u} R) :
    (∀ p : I × J, A p.1 p.2) ≃ₗ[R] (∀ i j, A i j) where
  toFun z i j := z (i, j)
  invFun z p := z p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

theorem intersection_zero (i : ι) :
    (∏ᶜ fun k : Fin 1 => U ((indexZero ι).symm i k)) = U i := by
  rw [SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf]
  simp only [indexZero, Equiv.coe_fn_symm_mk, iInf_const]

theorem intersection_one (p : ι × ι) :
    (∏ᶜ fun k : Fin 2 => U ((finTwoArrowEquiv ι).symm p k)) = U p.1 ⊓ U p.2 := by
  apply le_antisymm
  · exact le_inf (leOfHom (Pi.π _ 0)) (leOfHom (Pi.π _ 1))
  · apply leOfHom
    refine Pi.lift (fun k : Fin 2 => homOfLE ?_)
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

theorem intersection_two (p : ι × (ι × ι)) :
    (∏ᶜ fun k : Fin 3 => U ((indexTwo ι).symm p k)) = (U p.1 ⊓ U p.2.1) ⊓ U p.2.2 := by
  apply le_antisymm
  · exact le_inf (le_inf (leOfHom (Pi.π _ 0)) (leOfHom (Pi.π _ 1))) (leOfHom (Pi.π _ 2))
  · apply leOfHom
    refine Pi.lift (fun k : Fin 3 => homOfLE ?_)
    fin_cases k
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right

variable {R : Type u} [CommRing R] (F : X.Opensᵒᵖ ⥤ ModuleCat.{u} R)

def zeroPi :
    (∀ i : Fin 1 → ι, F.obj (op (∏ᶜ fun k => U (i k)))) ≃ₗ[R]
      (∀ i, F.obj (op (U i))) :=
  reindex F (fun i => ∏ᶜ fun k : Fin 1 => U (i k)) U (indexZero ι) (intersection_zero U)

def onePi :
    (∀ i : Fin 2 → ι, F.obj (op (∏ᶜ fun k => U (i k)))) ≃ₗ[R]
      (∀ i j, F.obj (op (U i ⊓ U j))) :=
  (reindex F (fun i => ∏ᶜ fun k : Fin 2 => U (i k))
    (fun p : ι × ι => U p.1 ⊓ U p.2) (finTwoArrowEquiv ι) (intersection_one U)).trans
      (curry (fun i j => F.obj (op (U i ⊓ U j))))

def twoPi :
    (∀ i : Fin 3 → ι, F.obj (op (∏ᶜ fun k => U (i k)))) ≃ₗ[R]
      (∀ i j k, F.obj (op ((U i ⊓ U j) ⊓ U k))) :=
  (reindex F (fun i => ∏ᶜ fun k : Fin 3 => U (i k))
    (fun p : ι × (ι × ι) => (U p.1 ⊓ U p.2.1) ⊓ U p.2.2)
    (indexTwo ι) (intersection_two U)).trans
    ((curry (fun i (p : ι × ι) => F.obj (op ((U i ⊓ U p.1) ⊓ U p.2)))).trans
      (LinearEquiv.piCongrRight fun i => curry (fun j k => F.obj (op ((U i ⊓ U j) ⊓ U k)))))

def zero : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 0 ≃ₗ[Γ(S, ⊤)]
    (∀ i, (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op (U i))) :=
  (SheafCohomology.Projective.BaseCechProducts.Scheme.Modules.baseCechXIsoPi π M U 0).toLinearEquiv.trans
    (zeroPi U (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M))

def one : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 1 ≃ₗ[Γ(S, ⊤)]
    (∀ i j, (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op (U i ⊓ U j))) :=
  (SheafCohomology.Projective.BaseCechProducts.Scheme.Modules.baseCechXIsoPi π M U 1).toLinearEquiv.trans
    (onePi U (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M))

def two : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 2 ≃ₗ[Γ(S, ⊤)]
    (∀ i j k, (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ((U i ⊓ U j) ⊓ U k))) :=
  (SheafCohomology.Projective.BaseCechProducts.Scheme.Modules.baseCechXIsoPi π M U 2).toLinearEquiv.trans
    (twoPi U (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M))

end Construction.CechTupleCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTuplePi

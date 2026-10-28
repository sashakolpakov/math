import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DenominatorUnits
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechEvaluation

/-! # Cech Fractions -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechFractions

noncomputable section

/-! The native dual exterior Koszul cocycle maps to literal fractions
on the ordered localization intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DenominatorUnits OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology

theorem hom_sum_apply {A B : AddCommGrpCat.{u}} {κ : Type*} [Fintype κ]
    (f : κ → (A ⟶ B)) (x : A) : (∑ k, f k).hom x = ∑ k, (f k).hom x :=
  (congrArg (fun h : A →+ B => h x) (map_sum AddCommGrpCat.homAddEquiv f Finset.univ)).trans
    (map_sum (AddMonoidHom.eval x) (fun k => (f k).hom) Finset.univ)

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {m : ℕ} (U : ULift.{u} (Fin m) → C) (P : Cᵒᵖ ⥤ CommRingCat.{u})
  (R : Type u) [CommRing R]
  (α : (Functor.const Cᵒᵖ).obj (CommRingCat.of R) ⟶ P)
  (s : Fin m → R) (hs : ∀ i, IsUnit ((α.app (op (U i))) (s i.down)))

def coordinate (q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    Module.Dual R (⋀[R]^q (Fin m → R)) →+ Cech.DenominatorUnits.ring U P a where
  toFun φ := Cech.DenominatorUnits.scalar U P R α a
      (φ (exteriorPower.ιMulti R q (fun j => (Pi.basisFun R (Fin m)) (a.val j).down))) *
    (↑((Cech.DenominatorUnits.denominator U P R α (fun i => s i.down) hs a)⁻¹) : Cech.DenominatorUnits.ring U P a)
  map_zero' := by simp
  map_add' φ ψ := by simp [map_add, add_mul]

theorem coordinate_differential (q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1))
    (φ : Module.Dual R (⋀[R]^q (Fin m → R))) :
    coordinate U P R α s hs (q + 1) a
      ((OrientedTopCohomology.dualComplex R s).d q (q + 1) φ) =
      ∑ k : Fin (q + 1), (-1 : ℤ) ^ k.val •
        Cech.DenominatorUnits.restriction U P a k (coordinate U P R α s hs q (a.delete k) φ) := by
  change Cech.DenominatorUnits.scalar U P R α a
      ((show Module.Dual R (⋀[R]^(q + 1) (Fin m → R)) from (OrientedTopCohomology.dualComplex R s).d q (q + 1) φ)
        (exteriorPower.ιMulti R (q + 1) (fun j => (Pi.basisFun R (Fin m)) (a.val j).down))) * _ = _
  rw [CechEvaluation.differential, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  change Cech.DenominatorUnits.scalar U P R α a
      (((-1 : R) ^ k.val * s (a.val k).down) *
        φ (exteriorPower.ιMulti R q (fun j => (Pi.basisFun R (Fin m)) (a.val (k.succAbove j)).down))) * _ = _
  simp only [map_mul, map_pow, map_neg, map_one, coordinate, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  have hα : Cech.DenominatorUnits.restriction U P a k (Cech.DenominatorUnits.scalar U P R α (a.delete k)
      (φ (exteriorPower.ιMulti R q (fun j => (Pi.basisFun R (Fin m)) ((a.delete k).val j).down)))) =
      Cech.DenominatorUnits.scalar U P R α a (φ (exteriorPower.ιMulti R q
        (fun j => (Pi.basisFun R (Fin m)) (a.val (k.succAbove j)).down))) :=
    Cech.DenominatorUnits.scalar_natural P R α ((AugmentedOrdered.Cech.face U q k).φ a) _
  rw [hα]
  rw [← Cech.DenominatorUnits.cancellation U P R α (fun i => s i.down) hs a k]
  ring

abbrev coefficient : Cᵒᵖ ⥤ AddCommGrpCat.{u} := P ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
abbrev source := ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
  (OrientedTopCohomology.dualComplex R s)

def component (q : ℕ) : (source R s).X q ⟶ AugmentedOrdered.Cech.object U (coefficient P) q :=
  Pi.lift (fun a => AddCommGrpCat.ofHom (coordinate U P R α s hs q a))

@[reassoc]
theorem component_comp_pi (q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    component U P R α s hs q ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q =>
        (coefficient P).obj (op ((AugmentedOrdered.Cech.formal U q).obj b))) a =
      AddCommGrpCat.ofHom (coordinate U P R α s hs q a) := Pi.lift_comp_π _ a

theorem component_differential (q : ℕ) :
    (source R s).d q (q + 1) ≫ component U P R α s hs (q + 1) =
      component U P R α s hs q ≫ AugmentedOrdered.Cech.differential U (coefficient P) q := by
  apply Pi.hom_ext
  intro a
  have hL := (Category.assoc ((source R s).d q (q + 1))
    (component U P R α s hs (q + 1))
    (Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1) =>
      (coefficient P).obj (op ((AugmentedOrdered.Cech.formal U (q + 1)).obj b))) a)).trans
    (congrArg (((source R s).d q (q + 1)) ≫ ·) (component_comp_pi U P R α s hs (q + 1) a))
  have hR : (component U P R α s hs q ≫ AugmentedOrdered.Cech.differential U (coefficient P) q) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1) =>
        (coefficient P).obj (op ((AugmentedOrdered.Cech.formal U (q + 1)).obj b))) a =
      ∑ k : Fin (q + 1), (-1 : ℤ) ^ k.val •
        (AddCommGrpCat.ofHom (coordinate U P R α s hs q (a.delete k)) ≫
          (coefficient P).map ((AugmentedOrdered.Cech.face U q k).φ a).op) := by
    calc
      _ = component U P R α s hs q ≫
          (∑ k : Fin (q + 1), (-1 : ℤ) ^ k.val •
            (Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q =>
              (coefficient P).obj (op ((AugmentedOrdered.Cech.formal U q).obj b))) (a.delete k) ≫
              (coefficient P).map ((AugmentedOrdered.Cech.face U q k).φ a).op)) :=
        (Category.assoc _ _ _).trans
          (congrArg ((component U P R α s hs q) ≫ ·) (AugmentedOrdered.CechCoordinates.differential_comp_pi U (coefficient P) q a))
      _ = _ := by
        simp only [CategoryTheory.Preadditive.comp_sum, CategoryTheory.Preadditive.comp_zsmul]
        apply Finset.sum_congr rfl
        intro k _
        exact congrArg (fun z => (-1 : ℤ) ^ k.val • z)
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ (coefficient P).map ((AugmentedOrdered.Cech.face U q k).φ a).op)
              (component_comp_pi U P R α s hs q (a.delete k))))
  refine hL.trans (Eq.trans ?_ hR.symm)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  exact (coordinate_differential U P R α s hs q a φ).trans
    (hom_sum_apply (fun k : Fin (q + 1) => (-1 : ℤ) ^ k.val •
      (AddCommGrpCat.ofHom (coordinate U P R α s hs q (a.delete k)) ≫
        (coefficient P).map ((AugmentedOrdered.Cech.face U q k).φ a).op)) φ).symm

def map : source R s ⟶ AugmentedOrdered.Cech.complex U (coefficient P) :=
  CochainComplex.ofHom (component U P R α s hs) (fun q => by
    dsimp only [AugmentedOrdered.Cech.complex]
    rw [CochainComplex.of_d]
    exact (component_differential U P R α s hs q).symm)

@[reassoc]
theorem map_comp_pi (q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    (CechFractions.map U P R α s hs).f q ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q =>
        (coefficient P).obj (op ((AugmentedOrdered.Cech.formal U q).obj b))) a =
      AddCommGrpCat.ofHom (coordinate U P R α s hs q a) :=
  Pi.lift_comp_π _ a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechFractions

import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Abelian.Opposite

/-! # Chain Resolution Opposite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOpposite

noncomputable section

/-! The opposite of an actual augmented chain resolution, with its original augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject Opposite

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

def singleComponentIso (Z : C) (i : ℕ) : ((CochainComplex.single₀ Cᵒᵖ).obj (op Z)).X i ≅
    (((ChainComplex.single₀ C).obj Z).op).X i := by
  cases i with
  | zero => exact Iso.refl (op Z)
  | succ i =>
      let hs := HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 (op Z)
        (i + 1) (Nat.succ_ne_zero i)
      let ht := (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 Z
        (i + 1) (Nat.succ_ne_zero i)).op
      exact hs.iso ht

def singleIso (Z : C) : (CochainComplex.single₀ Cᵒᵖ).obj (op Z) ≅ ((ChainComplex.single₀ C).obj Z).op :=
  HomologicalComplex.Hom.isoOfComponents (singleComponentIso Z) (by
    intro i j _
    change (singleComponentIso Z i).hom ≫ 0 = 0 ≫ (singleComponentIso Z j).hom
    simp)

variable (P : ChainComplex C ℕ) {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)

def augmentation : (CochainComplex.single₀ Cᵒᵖ).obj (op Z) ⟶ P.op :=
  (singleIso Z).hom ≫ (HomologicalComplex.opFunctor C (.down ℕ)).map ε.op

theorem augmentation_zero : (augmentation P ε).f 0 = (ε.f 0).op := by
  change 𝟙 _ ≫ (ε.f 0).op = (ε.f 0).op
  exact Category.id_comp _

instance augmentation_quasiIso [QuasiIso ε] : QuasiIso (augmentation P ε) := by
  let h : QuasiIso ((HomologicalComplex.opFunctor C (.down ℕ)).map ε.op) :=
    (HomologicalComplex.quasiIso_opFunctor_map_iff ε).mpr inferInstance
  let : IsIso (singleIso Z).hom := (singleIso Z).isIso_hom
  let he : QuasiIso (singleIso Z).hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := he) (hφ' := h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOpposite

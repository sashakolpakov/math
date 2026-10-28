import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Zero Kernels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels

noncomputable section

/-!
# IntegralComparison: the original degree-zero Ext functor preserves cycle kernels
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0

theorem map_mono {Y Z : C} (g : Y ⟶ Z) [Mono g] : Mono ((F).map g) :=
  (ModuleCat.mono_iff_injective _).mpr (Ext.postcomp_mk₀_injective_of_mono X g)

theorem map_exact (S : ShortComplex C) (hS : S.Exact) [Mono S.f] : (S.map F).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change Ext.{z} X S.X₂ 0 at x
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  have hg : g ≫ S.g = 0 := by
    apply (Ext.mk₀_eq_zero_iff (g ≫ S.g)).mp
    exact (Ext.mk₀_comp_mk₀ g S.g).symm.trans hx
  let h := hS.fIsKernel
  let y := h.lift (KernelFork.ofι g hg)
  refine ⟨Ext.mk₀ y, ?_⟩
  exact (Ext.mk₀_comp_mk₀ y S.f).trans
    (congrArg (fun a : X ⟶ S.X₂ => (Ext.mk₀ a : Ext.{z} X S.X₂ 0))
      (h.fac (KernelFork.ofι g hg) WalkingParallelPair.zero))

def cycleKernel (S : ShortComplex C) :
    IsLimit (KernelFork.ofι ((F).map S.iCycles) (show (F).map S.iCycles ≫ (F).map S.g = 0 by
      rw [← (F).map_comp, S.iCycles_g, (F).map_zero])) := by
  let T := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel T S.cyclesIsKernel
  let : Mono (T.map F).f := map_mono R X S.iCycles
  exact (map_exact R X T hT).fIsKernel

theorem cycleKernel_lift (S : ShortComplex C) :
    (cycleKernel R X S).lift (KernelFork.ofι ((F).map S.f)
      (show (F).map S.f ≫ (F).map S.g = 0 by rw [← (F).map_comp, S.zero, (F).map_zero])) =
      (F).map S.toCycles := by
  let : Mono ((F).map S.iCycles) := map_mono R X S.iCycles
  apply (cancel_mono ((F).map S.iCycles)).mp
  have h : (F).map S.toCycles ≫ (F).map S.iCycles = (F).map S.f :=
    ((F).map_comp S.toCycles S.iCycles).symm.trans (congrArg (F).map S.toCycles_i)
  exact ((cycleKernel R X S).fac _ WalkingParallelPair.zero).trans h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels

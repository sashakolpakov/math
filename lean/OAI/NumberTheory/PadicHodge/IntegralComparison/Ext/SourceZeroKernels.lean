import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Source Zero Kernels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceZeroKernels

noncomputable section

/-! Contravariant degree-zero original Ext preserves the cycle kernels of the opposite source resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0

theorem map_mono {A B : Cᵒᵖ} (g : A ⟶ B) [Mono g] : Mono ((F).map g) :=
  (ModuleCat.mono_iff_injective _).mpr (Ext.precomp_mk₀_injective_of_epi Y g.unop)

theorem map_exact (S : ShortComplex Cᵒᵖ) (hS : S.Exact) [Mono S.f] : (S.map F).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change Ext.{z} S.X₂.unop Y 0 at x
  obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  have hg : S.g.unop ≫ g = 0 :=
    (Ext.mk₀_eq_zero_iff _).mp ((Ext.mk₀_comp_mk₀ S.g.unop g).symm.trans hx)
  let : Epi S.unop.g := inferInstanceAs (Epi S.f.unop)
  let h := hS.unop.gIsCokernel
  let y := h.desc (CokernelCofork.ofπ g hg)
  refine ⟨Ext.mk₀ y, ?_⟩
  exact (Ext.mk₀_comp_mk₀ S.f.unop y).trans
    (congrArg (fun a : S.X₂.unop ⟶ Y => (Ext.mk₀ a : Ext.{z} S.X₂.unop Y 0))
      (h.fac (CokernelCofork.ofπ g hg) WalkingParallelPair.one))

def cycleKernel (S : ShortComplex Cᵒᵖ) :
    IsLimit (KernelFork.ofι ((F).map S.iCycles) (show (F).map S.iCycles ≫ (F).map S.g = 0 by
      rw [← (F).map_comp, S.iCycles_g, (F).map_zero])) := by
  let T := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel T S.cyclesIsKernel
  let : Mono (T.map F).f := map_mono R Y S.iCycles
  exact (map_exact R Y T hT).fIsKernel

theorem cycleKernel_lift (S : ShortComplex Cᵒᵖ) :
    (cycleKernel R Y S).lift (KernelFork.ofι ((F).map S.f)
      (show (F).map S.f ≫ (F).map S.g = 0 by rw [← (F).map_comp, S.zero, (F).map_zero])) =
      (F).map S.toCycles := by
  let : Mono ((F).map S.iCycles) := map_mono R Y S.iCycles
  apply (cancel_mono ((F).map S.iCycles)).mp
  have h : (F).map S.toCycles ≫ (F).map S.iCycles = (F).map S.f :=
    ((F).map_comp S.toCycles S.iCycles).symm.trans (congrArg (F).map S.toCycles_i)
  exact ((cycleKernel R Y S).fac _ WalkingParallelPair.zero).trans h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceZeroKernels

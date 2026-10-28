import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Short Exact Homology Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ShortExactHomologyKernel

noncomputable section

/-!
# IntegralComparison: the kernel description when the previous cohomology map is surjective
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
  (S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)

include hS in
theorem mono_zero : Mono (HomologicalComplex.homologyMap S.f 0) := by
  let : Mono S.f := hS.mono_f
  exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (fun i => by
    change ¬ i + 1 = 0
    omega)

theorem connecting_zero (i : ℕ) [Epi (HomologicalComplex.homologyMap S.g i)] :
    hS.δ i (i + 1) rfl = 0 := by
  rw [← cancel_epi (HomologicalComplex.homologyMap S.g i), CategoryTheory.Limits.comp_zero]
  exact hS.comp_δ i (i + 1) rfl

include hS in
theorem mono_succ (i : ℕ) [Epi (HomologicalComplex.homologyMap S.g i)] :
    Mono (HomologicalComplex.homologyMap S.f (i + 1)) :=
  (hS.homology_exact₁ i (i + 1) rfl).mono_g (connecting_zero S hS i)

def kernelLinearEquiv (T : ShortComplex (ModuleCat.{v} R)) (hT : T.Exact) [Mono T.f] :
    T.X₁ ≃ₗ[R] LinearMap.ker T.g.hom :=
  (LinearEquiv.ofInjective T.f.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)).trans
    (LinearEquiv.ofEq _ _ hT.moduleCat_range_eq_ker)

theorem kernelLinearEquiv_apply (T : ShortComplex (ModuleCat.{v} R)) (hT : T.Exact) [Mono T.f]
    (x : T.X₁) : (kernelLinearEquiv T hT x).val = T.f x := rfl

def homologyKernelLinearEquiv (i : ℕ) [Mono (HomologicalComplex.homologyMap S.f i)] :
    S.X₁.homology i ≃ₗ[R] LinearMap.ker (HomologicalComplex.homologyMap S.g i).hom := by
  let T := S.map (HomologicalComplex.homologyFunctor _ _ i)
  letI : Mono T.f := (inferInstance : Mono (HomologicalComplex.homologyMap S.f i))
  exact kernelLinearEquiv T (hS.homology_exact₂ i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ShortExactHomologyKernel

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cochain Cycle -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainCycle.CochainCycleCorrection

noncomputable section

/-!
# Correcting a lifted cochain to a cycle

For a left exact sequence of module complexes, a lifted cochain whose
image is a cycle can be corrected by a cochain in the first complex,
provided the next-degree cohomology of that first complex vanishes.
This is the algebraic correction step in descent of local primitives.
-/

open _root_.CategoryTheory

universe u v

variable (R : Type u) [Ring R]
  (S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ)) (n : ℕ)

def degree (j : ℕ) : ShortComplex (ModuleCat.{v} R) :=
  S.map (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℕ) j)

theorem exists_cycle
    (hS : (degree R S (n + 1)).Exact) [Mono (S.f.f (n + 2))]
    (hA : (S.X₁.sc' n (n + 1) (n + 2)).Exact)
    (y : S.X₂.X n) (hy : S.g.f (n + 1) (S.X₂.d n (n + 1) y) = 0) :
    ∃ y' : S.X₂.X n, S.X₂.d n (n + 1) y' = 0 ∧ S.g.f n y' = S.g.f n y := by
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff (degree R S (n + 1))).mp hS
    (S.X₂.d n (n + 1) y) hy
  change S.X₁.X (n + 1) at z
  change S.f.f (n + 1) z = S.X₂.d n (n + 1) y at hz
  have hdz : S.X₁.d (n + 1) (n + 2) z = 0 := by
    apply (ModuleCat.mono_iff_injective (S.f.f (n + 2))).mp inferInstance
    have hc := congrArg (fun f => f z) (S.f.comm (n + 1) (n + 2))
    change S.X₂.d (n + 1) (n + 2) (S.f.f (n + 1) z) =
      S.f.f (n + 2) (S.X₁.d (n + 1) (n + 2) z) at hc
    rw [← hc, hz]
    exact (congrArg (fun f => f y) (S.X₂.d_comp_d n (n + 1) (n + 2))).trans
      (S.f.f (n + 2)).hom.map_zero.symm
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff (S.X₁.sc' n (n + 1) (n + 2))).mp hA z hdz
  change S.X₁.X n at w
  change S.X₁.d n (n + 1) w = z at hw
  refine ⟨y - S.f.f n w, ?_, ?_⟩
  · rw [map_sub]
    have hc := congrArg (fun f => f w) (S.f.comm n (n + 1))
    change S.X₂.d n (n + 1) (S.f.f n w) = S.f.f (n + 1) (S.X₁.d n (n + 1) w) at hc
    rw [hc, hw, hz, sub_self]
  · rw [map_sub]
    have hz' := congrArg (fun f => f.f n w) S.zero
    change S.g.f n (S.f.f n w) = 0 at hz'
    rw [hz', sub_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainCycle.CochainCycleCorrection

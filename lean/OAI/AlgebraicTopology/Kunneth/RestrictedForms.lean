import OAI.Analysis.DifferentialForms.Manifold.DeRham
import OAI.AlgebraicTopology.DeRham.Comparison.RadialHomotopyIdentity
import OAI.AlgebraicTopology.DeRham.Comparison.RadialHomotopySmooth
import Mathlib.Analysis.Convex.Star

/-! # Restricted Forms -/

namespace OAI.AlgebraicTopology.Kunneth.RestrictedForms

noncomputable section

/-! The de Rham complex of restrictions of smooth forms to a full-dimensional set. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Set
open scoped ContDiff Interval

namespace Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance restrictedFormsAddGroup (n : ℕ) : AddCommGroup (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance
local instance restrictedFormsModule (n : ℕ) : Module ℂ (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance

def formsVanishingOn (S : Set E) (n : ℕ) : Submodule ℂ (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) where
  carrier := {a | ∀ x ∈ S, a x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' ha hb x hx := by rw [OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.add_apply, ha x hx, hb x hx, add_zero]
  smul_mem' c a ha x hx := by
    rw [OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.smul_apply, ha x hx]
    ext v
    change c * (0 : ℂ) = 0
    exact mul_zero c

/-- Two representatives define the same restricted form precisely when their
covector values agree on the specified set. -/
abbrev RestrictedForm (S : Set E) (n : ℕ) := OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n ⧸ formsVanishingOn S n

def restrictForm (S : Set E) (n : ℕ) : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n →ₗ[ℂ] RestrictedForm S n :=
  (formsVanishingOn S n).mkQ

theorem restrictForm_eq_iff (S : Set E) (n : ℕ) (a b : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) :
    restrictForm S n a = restrictForm S n b ↔ ∀ x ∈ S, a x = b x := by
  change Submodule.Quotient.mk a = Submodule.Quotient.mk b ↔ _
  rw [Submodule.Quotient.eq]
  change (∀ x ∈ S, (a - b) x = 0) ↔ _
  simp only [OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.sub_apply, sub_eq_zero]

theorem d_mem_formsVanishingOn {S : Set E} (hS : UniqueDiffOn ℝ S) {n : ℕ}
    {a : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n} (ha : a ∈ formsVanishingOn S n) :
    OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a ∈ formsVanishingOn S (n + 1) := by
  intro x hx
  have hzero : fderivWithin ℝ (a : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) S x = 0 := by
    have he : EqOn (a : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) (fun _ => 0) S := ha
    rw [fderivWithin_congr' he hx, fderivWithin_const_apply]
  have hd := fderivWithin_eq_fderiv (hS x hx)
    (a.smooth.differentiable (by simp) x)
  change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (a : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n) x) = 0
  rw [← hd, hzero]
  ext v
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  change (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • (0 : ℂ)) = 0
  simp only [smul_zero, Finset.sum_const_zero]

def restrictedFormD {S : Set E} (hS : UniqueDiffOn ℝ S) (n : ℕ) :
    RestrictedForm S n →ₗ[ℂ] RestrictedForm S (n + 1) :=
  (formsVanishingOn S n).mapQ (formsVanishingOn S (n + 1)) OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d
    (fun _ ha => d_mem_formsVanishingOn hS ha)

@[simp] theorem restrictedFormD_restrict {S : Set E} (hS : UniqueDiffOn ℝ S) (n : ℕ)
    (a : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) :
    restrictedFormD hS n (restrictForm S n a) = restrictForm S (n + 1) (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a) := rfl

theorem restrictedFormD_squared {S : Set E} (hS : UniqueDiffOn ℝ S) (n : ℕ) :
    (restrictedFormD hS (n + 1)).comp (restrictedFormD hS n) = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨a, rfl⟩ := (formsVanishingOn S n).mkQ_surjective a
  change restrictedFormD hS (n + 1) (restrictedFormD hS n (restrictForm S n a)) = 0
  rw [restrictedFormD_restrict, restrictedFormD_restrict, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_d, map_zero]

def restrictedDeRhamComplex {S : Set E} (hS : UniqueDiffOn ℝ S) :
    CochainComplex (ModuleCat ℂ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℂ (RestrictedForm S n))
    (fun n => ModuleCat.ofHom (restrictedFormD hS n))
    (fun n => ModuleCat.hom_ext (restrictedFormD_squared hS n))

variable [FiniteDimensional ℝ E]

def radialPrimitive {n : ℕ} (a : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1)) : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n :=
  OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth (DeRham.Comparison.RadialOne.radialHomotopy (a : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)))
    (DeRham.Comparison.RadialHomotopySmooth.contDiff_radialHomotopy a.smooth)

/-- The explicit radial primitive works for a form closed just on the set. -/
theorem radialPrimitive_d_on {S : Set E} (hS : StarConvex ℝ (0 : E) S)
    {n : ℕ} (a : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1))
    (ha : ∀ x ∈ S, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a x = 0) {x : E} (hx : x ∈ S) :
    OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (radialPrimitive a) x = a x := by
  have h := DeRham.Comparison.RadialHomotopyIdentity.radialHomotopy_identity (a.smooth.of_le (by simp)) x
  have hz : DeRham.Comparison.RadialOne.radialHomotopy (extDeriv (a : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1))) x = 0 := by
    rw [DeRham.Comparison.RadialOne.radialHomotopy]
    have he : (∫ t in (0 : ℝ)..1,
        DeRham.Comparison.RadialOne.radialIntegrand (extDeriv (a : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1))) x t) =
        ∫ _t in (0 : ℝ)..1, (0 : E [⋀^Fin (n + 1)]→L[ℝ] ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      have hd : extDeriv (a : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)) (t • x) = 0 :=
        ha (t • x) (hS.smul_mem hx ht'.1 ht'.2)
      rw [DeRham.Comparison.RadialOne.radialIntegrand, hd]
      rw [ContinuousAlternatingMap.curryLeft_zero]
      exact smul_zero _
    rw [he, intervalIntegral.integral_zero]
  rw [hz, add_zero] at h
  exact h

/-- Positive-degree closed restricted forms have actual restricted primitives. -/
theorem restrictedFormD_exact {S : Set E} (hS : UniqueDiffOn ℝ S)
    (hstar : StarConvex ℝ (0 : E) S) (n : ℕ) (a : RestrictedForm S (n + 1))
    (ha : restrictedFormD hS (n + 1) a = 0) :
    ∃ b : RestrictedForm S n, restrictedFormD hS n b = a := by
  obtain ⟨a, rfl⟩ := (formsVanishingOn S (n + 1)).mkQ_surjective a
  change restrictForm S (n + 2) (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a) = 0 at ha
  have ha' : ∀ x ∈ S, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a x = 0 :=
    (Submodule.Quotient.mk_eq_zero (formsVanishingOn S (n + 2))).mp ha
  refine ⟨restrictForm S n (radialPrimitive a), ?_⟩
  rw [restrictedFormD_restrict]
  apply (restrictForm_eq_iff S (n + 1) (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (radialPrimitive a)) a).mpr
  intro x hx
  exact radialPrimitive_d_on hstar a ha' hx

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.RestrictedForms

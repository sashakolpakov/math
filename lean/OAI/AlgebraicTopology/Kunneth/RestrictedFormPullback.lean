import OAI.AlgebraicTopology.Kunneth.RestrictedForms
import OAI.Analysis.DifferentialForms.Manifold.Vectors

/-! # Restricted Form Pullback -/

namespace OAI.AlgebraicTopology.Kunneth.RestrictedFormPullback

noncomputable section

/-! Pullback and its naturality on the actual restricted de Rham complex. -/

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace Constructions

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

local instance restrictedPullbackFormsAddGroup (n : ℕ) : AddCommGroup (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance
local instance restrictedPullbackFormsModule (n : ℕ) : Module ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance

def restrictedFormEval {S : Set E} (n : ℕ) (x : E) (hx : x ∈ S) :
    RestrictedForms.Constructions.RestrictedForm S n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  (RestrictedForms.Constructions.formsVanishingOn S n).liftQ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.eval x) (fun _ ha => ha x hx)

@[simp] theorem restrictedFormEval_restrict {S : Set E} (n : ℕ) (x : E) (hx : x ∈ S)
    (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) :
    restrictedFormEval n x hx (RestrictedForms.Constructions.restrictForm S n a) = a x := rfl

theorem restrictedForm_ext {S : Set E} {n : ℕ} {a b : RestrictedForms.Constructions.RestrictedForm S n}
    (h : ∀ x (hx : x ∈ S), restrictedFormEval n x hx a = restrictedFormEval n x hx b) :
    a = b := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S n).mkQ_surjective a
  obtain ⟨b, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S n).mkQ_surjective b
  exact (RestrictedForms.Constructions.restrictForm_eq_iff S n a b).mpr h

theorem pullback_mem_formsVanishingOn {S : Set E} {T : Set F} {n : ℕ}
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hmap : MapsTo f S T)
    {a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm F n} (ha : a ∈ RestrictedForms.Constructions.formsVanishingOn T n) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf a ∈ RestrictedForms.Constructions.formsVanishingOn S n := by
  intro x hx
  rw [Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback_apply, ha (f x) (hmap hx)]
  ext v
  rfl

def restrictedFormPullback {S : Set E} {T : Set F}
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hmap : MapsTo f S T) (n : ℕ) :
    RestrictedForms.Constructions.RestrictedForm T n →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm S n :=
  (RestrictedForms.Constructions.formsVanishingOn T n).mapQ (RestrictedForms.Constructions.formsVanishingOn S n) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf)
    (fun _ ha => pullback_mem_formsVanishingOn f hf hmap ha)

@[simp] theorem restrictedFormPullback_restrict {S : Set E} {T : Set F}
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hmap : MapsTo f S T) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm F n) :
    restrictedFormPullback f hf hmap n (RestrictedForms.Constructions.restrictForm T n a) =
      RestrictedForms.Constructions.restrictForm S n (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf a) := rfl

theorem restrictedFormPullback_d {S : Set E} {T : Set F}
    (hS : UniqueDiffOn ℝ S) (hT : UniqueDiffOn ℝ T)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hmap : MapsTo f S T) (n : ℕ)
    (a : RestrictedForms.Constructions.RestrictedForm T n) :
    RestrictedForms.Constructions.restrictedFormD hS n (restrictedFormPullback f hf hmap n a) =
      restrictedFormPullback f hf hmap (n + 1) (RestrictedForms.Constructions.restrictedFormD hT n a) := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn T n).mkQ_surjective a
  change RestrictedForms.Constructions.restrictForm S (n + 1) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf a)) =
    RestrictedForms.Constructions.restrictForm S (n + 1) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a))
  rw [Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_pullback]

theorem restrictedFormPullback_id (S : Set E) (n : ℕ) (a : RestrictedForms.Constructions.RestrictedForm S n) :
    restrictedFormPullback id contDiff_id (mapsTo_id S) n a = a := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S n).mkQ_surjective a
  change restrictedFormPullback id contDiff_id (mapsTo_id S) n (RestrictedForms.Constructions.restrictForm S n a) = _
  rw [restrictedFormPullback_restrict, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback_id]
  rfl

theorem restrictedFormPullback_comp {S : Set E} {T : Set F} {U : Set G}
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hmap : MapsTo f S T)
    (g : F → G) (hg : ContDiff ℝ ∞ g) (hmapg : MapsTo g T U)
    (n : ℕ) (a : RestrictedForms.Constructions.RestrictedForm U n) :
    restrictedFormPullback (g ∘ f) (hg.comp hf) (hmapg.comp hmap) n a =
      restrictedFormPullback f hf hmap n (restrictedFormPullback g hg hmapg n a) := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn U n).mkQ_surjective a
  change RestrictedForms.Constructions.restrictForm S n (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback (g ∘ f) (hg.comp hf) a) =
    RestrictedForms.Constructions.restrictForm S n (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback g hg a))
  rw [Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback_comp]

/-- Pullback on restrictions depends only on the map on the set. -/
theorem restrictedFormPullback_congr {S : Set E} {T : Set F}
    (hS : UniqueDiffOn ℝ S) (f g : E → F) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hmapf : MapsTo f S T) (hmapg : MapsTo g S T) (heq : EqOn f g S)
    (n : ℕ) (a : RestrictedForms.Constructions.RestrictedForm T n) :
    restrictedFormPullback f hf hmapf n a = restrictedFormPullback g hg hmapg n a := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn T n).mkQ_surjective a
  change RestrictedForms.Constructions.restrictForm S n (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf a) =
    RestrictedForms.Constructions.restrictForm S n (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback g hg a)
  rw [RestrictedForms.Constructions.restrictForm_eq_iff]
  intro x hx
  have hd : fderiv ℝ f x = fderiv ℝ g x := by
    rw [← fderivWithin_eq_fderiv (hS x hx) (hf.differentiable (by simp) x),
      ← fderivWithin_eq_fderiv (hS x hx) (hg.differentiable (by simp) x)]
    exact fderivWithin_congr' heq hx
  rw [Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback_apply, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback_apply, heq hx, hd]

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.RestrictedFormPullback

import OAI.AlgebraicTopology.Kunneth.WedgeAlgebra
import OAI.AlgebraicTopology.Kunneth.RestrictedFormPullback

/-! # Restricted Wedge -/

namespace OAI.AlgebraicTopology.Kunneth.RestrictedWedge

noncomputable section

/-! The genuine exterior product on restrictions of smooth forms. -/

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q : ℕ}

local instance restrictedWedgeFormsAddGroup (n : ℕ) : AddCommGroup (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance
local instance restrictedWedgeFormsModule (n : ℕ) : Module ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance

theorem normedWedge_vanishing_left {S : Set E} (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q)
    (ha : a ∈ RestrictedForms.Constructions.formsVanishingOn S p) : WedgeAlgebra.Constructions.normedWedge a b ∈ RestrictedForms.Constructions.formsVanishingOn S (p + q) := by
  intro x hx
  rw [WedgeAlgebra.Constructions.normedWedge_apply, ha x hx, WedgeAlgebra.Constructions.covectorWedge_zero_left]

theorem normedWedge_vanishing_right {S : Set E} (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q)
    (hb : b ∈ RestrictedForms.Constructions.formsVanishingOn S q) : WedgeAlgebra.Constructions.normedWedge a b ∈ RestrictedForms.Constructions.formsVanishingOn S (p + q) := by
  intro x hx
  rw [WedgeAlgebra.Constructions.normedWedge_apply, hb x hx, WedgeAlgebra.Constructions.covectorWedge_zero_right]

def restrictedWedgeRight (S : Set E) (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) :
    RestrictedForms.Constructions.RestrictedForm S q →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm S (p + q) :=
  (RestrictedForms.Constructions.formsVanishingOn S q).liftQ
    ((RestrictedForms.Constructions.restrictForm S (p + q)).comp (WedgeAlgebra.Constructions.normedWedgeLM (E := E) p q a))
    (fun b hb => (Submodule.Quotient.mk_eq_zero (RestrictedForms.Constructions.formsVanishingOn S (p + q))).mpr
      (normedWedge_vanishing_right a b hb))

@[simp] theorem restrictedWedgeRight_restrict (S : Set E) (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p)
    (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q) :
    restrictedWedgeRight S a (RestrictedForms.Constructions.restrictForm S q b) = RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedge a b) := rfl

def restrictedWedgeOnSmooth (S : Set E) (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm S q →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm S (p + q) where
  toFun := restrictedWedgeRight S
  map_add' a a' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S q).mkQ_surjective b
    change RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedgeLM (E := E) p q (a + a') b) =
      RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedgeLM (E := E) p q a b) +
        RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedgeLM (E := E) p q a' b)
    rw [map_add]
    exact (RestrictedForms.Constructions.restrictForm S (p + q)).map_add _ _
  map_smul' c a := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S q).mkQ_surjective b
    change RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedgeLM (E := E) p q (c • a) b) =
      c • RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedgeLM (E := E) p q a b)
    rw [map_smul]
    exact (RestrictedForms.Constructions.restrictForm S (p + q)).map_smul c _

def restrictedWedge (S : Set E) (p q : ℕ) :
    RestrictedForms.Constructions.RestrictedForm S p →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm S q →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm S (p + q) :=
  (RestrictedForms.Constructions.formsVanishingOn S p).liftQ (restrictedWedgeOnSmooth S p q) (by
    intro a ha
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S q).mkQ_surjective b
    change RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedge a b) = 0
    exact (Submodule.Quotient.mk_eq_zero (RestrictedForms.Constructions.formsVanishingOn S (p + q))).mpr
      (normedWedge_vanishing_left a b ha))

@[simp] theorem restrictedWedge_restrict (S : Set E) (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q) :
    restrictedWedge S p q (RestrictedForms.Constructions.restrictForm S p a) (RestrictedForms.Constructions.restrictForm S q b) =
      RestrictedForms.Constructions.restrictForm S (p + q) (WedgeAlgebra.Constructions.normedWedge a b) := rfl

def restrictedFormDegreeCast (S : Set E) {n m : ℕ} (h : n = m) :
    RestrictedForms.Constructions.RestrictedForm S n ≃ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm S m := h ▸ LinearEquiv.refl ℂ (RestrictedForms.Constructions.RestrictedForm S n)

@[simp] theorem restrictedFormDegreeCast_restrict (S : Set E) {n m : ℕ} (h : n = m)
    (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) :
    restrictedFormDegreeCast S h (RestrictedForms.Constructions.restrictForm S n a) =
      RestrictedForms.Constructions.restrictForm S m (WedgeAlgebra.Constructions.normedFormDegreeCast h a) := by
  subst m
  rfl

/-- The product rule holds when the right factor is closed only on the restricted set. -/
theorem restrictedWedge_d_of_right_closed {S : Set E} (hS : UniqueDiffOn ℝ S)
    (a : RestrictedForms.Constructions.RestrictedForm S p) (b : RestrictedForms.Constructions.RestrictedForm S q) (hb : RestrictedForms.Constructions.restrictedFormD hS q b = 0) :
    RestrictedForms.Constructions.restrictedFormD hS (p + q) (restrictedWedge S p q a b) =
      restrictedFormDegreeCast S (by omega)
        (restrictedWedge S (p + 1) q (RestrictedForms.Constructions.restrictedFormD hS p a) b) := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S p).mkQ_surjective a
  obtain ⟨b, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S q).mkQ_surjective b
  change RestrictedForms.Constructions.restrictForm S (q + 1) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d b) = 0 at hb
  have hb' : ∀ x ∈ S, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d b x = 0 :=
    (Submodule.Quotient.mk_eq_zero (RestrictedForms.Constructions.formsVanishingOn S (q + 1))).mp hb
  change RestrictedForms.Constructions.restrictForm S (p + q + 1) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (WedgeAlgebra.Constructions.normedWedge a b)) =
    restrictedFormDegreeCast S (by omega)
      (RestrictedForms.Constructions.restrictForm S (p + 1 + q) (WedgeAlgebra.Constructions.normedWedge (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a) b))
  rw [restrictedFormDegreeCast_restrict, RestrictedForms.Constructions.restrictForm_eq_iff]
  intro x hx
  exact WedgeAlgebra.Constructions.normedWedge_d_of_right_closed a b (hb' x hx)

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.RestrictedWedge

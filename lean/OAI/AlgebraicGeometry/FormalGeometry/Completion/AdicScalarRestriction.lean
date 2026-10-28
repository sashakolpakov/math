import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Maps

/-! # Adic Scalar Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicScalarRestriction.Construction

noncomputable section

/-! Adic completion along an ideal of the base agrees with completion along its extension.
This permits Artin--Rees arguments on the actual affine chart rings. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Extending the base ideal and restricting scalars give the same quotient module. -/
def adicScalarRestrictionQuotientEquiv (n : ℕ) :
    (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R]
      M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [← Ideal.map_pow]
    exact (Ideal.smul_restrictScalars (I ^ n) (⊤ : Submodule S M)).symm)).trans
      (Submodule.Quotient.restrictScalarsEquiv R _)

theorem adicScalarRestrictionQuotientEquiv_mk (n : ℕ) (m : M) :
    adicScalarRestrictionQuotientEquiv (S := S) I M n (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := rfl

theorem adicScalarRestrictionQuotientEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) M h
        (adicScalarRestrictionQuotientEquiv (S := S) I M n x) =
      adicScalarRestrictionQuotientEquiv (S := S) I M m (AdicCompletion.transitionMap I M h x) := by
  induction x using Submodule.Quotient.induction_on with | _ x => rfl

/-- Completion at the base ideal equals completion at its extended ideal on the same module. -/
def adicScalarRestrictionEquiv :
    AdicCompletion I M ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) M where
  toFun x := ⟨fun n => adicScalarRestrictionQuotientEquiv (S := S) I M n (x.val n), by
    intro m n h
    rw [adicScalarRestrictionQuotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n => (adicScalarRestrictionQuotientEquiv (S := S) I M n).symm (x.val n), by
    intro m n h
    apply (adicScalarRestrictionQuotientEquiv (S := S) I M m).injective
    rw [← adicScalarRestrictionQuotientEquiv_transition, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, x.property h]⟩
  left_inv x := by apply AdicCompletion.ext; intro n; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by apply AdicCompletion.ext; intro n; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by apply AdicCompletion.ext; intro n; exact map_add _ _ _
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    exact (adicScalarRestrictionQuotientEquiv (S := S) I M n).map_smul r (x.val n)

theorem adicScalarRestrictionEquiv_apply_val (x : AdicCompletion I M) (n : ℕ) :
    (adicScalarRestrictionEquiv (S := S) I M x).val n =
      adicScalarRestrictionQuotientEquiv (S := S) I M n (x.val n) := rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicScalarRestriction.Construction

import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Orthogonal Projectors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OrthogonalProjectors.Construction

noncomputable section

/-!
A complete orthogonal family of group endomorphisms gives a product
decomposition into its fixed subgroups. Idempotence is derived from
orthogonality and completeness, and the inverse is the product of the
included fixed components.
-/

open scoped BigOperators

variable {I G : Type*} [Fintype I] [CommGroup G]
  (p : I → (G →* G))
  (horth : ∀ i j, i ≠ j → ∀ x, p i (p j x) = 1)
  (hcomplete : ∀ x, (∏ i, p i x) = x)

include horth hcomplete in
theorem orthogonal_projector_idempotent (i : I) (x : G) : p i (p i x) = p i x := by
  classical
  have hp : (∏ j, p i (p j x)) = p i (p i x) := by
    apply Finset.prod_eq_single i
    · intro j _ hji
      exact horth i j hji.symm x
    · simp
  rw [← hp, ← map_prod, hcomplete]

def orthogonalProjectorEquiv : G ≃* (∀ i, (p i).eqLocus (MonoidHom.id G)) where
  toFun x i := ⟨p i x, orthogonal_projector_idempotent p horth hcomplete i x⟩
  invFun x := ∏ i, (x i).val
  left_inv := hcomplete
  right_inv x := by
    classical
    funext i
    apply Subtype.ext
    change p i (∏ j, (x j).val) = (x i).val
    rw [map_prod]
    calc
      (∏ j, p i (x j).val) = p i (x i).val := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          have hj : p j (x j).val = (x j).val := (x j).property
          rw [← hj]
          exact horth i j hji.symm (x j).val
        · simp
      _ = (x i).val := (x i).property
  map_mul' x y := by
    funext i
    exact Subtype.ext ((p i).map_mul x y)

theorem orthogonalProjectorEquiv_apply (x : G) (i : I) :
    (orthogonalProjectorEquiv p horth hcomplete x i).val = p i x := rfl

theorem orthogonalProjectorEquiv_symm_apply (x : ∀ i, (p i).eqLocus (MonoidHom.id G)) :
    (orthogonalProjectorEquiv p horth hcomplete).symm x = ∏ i, (x i).val := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OrthogonalProjectors.Construction

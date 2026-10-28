import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OrthogonalProjectors
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Split Pairing Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitPairingFormula.Construction

noncomputable section

/-!
Recover an alternating pairing from conjugate-adjoint projectors. The
formula follows from completeness, idempotence and adjointness; it is not
an extra compatibility assumption in the kernel construction.
-/

open scoped BigOperators

variable {I G W : Type*} [Fintype I] [CommGroup G] [CommGroup W]
  (b : G →* (G →* W)) (p : I ⊕ I → (G →* G))
  (horth : ∀ i j, i ≠ j → ∀ x, p i (p j x) = 1)
  (hcomplete : ∀ x, (∏ i, p i x) = x)
  (hadjoint : ∀ i x y, b (p i x) y = b x (p (Sum.swap i) y))

include horth hcomplete hadjoint in
theorem pairing_projector_restrict (i : I ⊕ I) (x y : G) :
    b (p i x) y = b (p i x) (p (Sum.swap i) y) := by
  calc
    _ = b (p i (p i x)) y := congrArg (fun z => b z y)
      (OrthogonalProjectors.Construction.orthogonal_projector_idempotent p horth hcomplete i x).symm
    _ = _ := hadjoint i (p i x) y

include horth hcomplete hadjoint in
theorem pairing_projector_product (x y : G) :
    b x y = ∏ i, b (p i x) (p (Sum.swap i) y) := by
  calc
    b x y = b (∏ i, p i x) y := congrArg (fun z => b z y) (hcomplete x).symm
    _ = ∏ i, b (p i x) y := by simp only [map_prod, MonoidHom.finsetProd_apply]
    _ = _ := Finset.prod_congr rfl (fun i _ => pairing_projector_restrict b p horth hcomplete hadjoint i x y)

include horth hcomplete hadjoint in
theorem pairing_split_projector_formula
    (hskew : ∀ x y, b y x = (b x y)⁻¹) (x y : G) :
    b x y = ∏ i, b (p (Sum.inl i) x) (p (Sum.inr i) y) /
      b (p (Sum.inl i) y) (p (Sum.inr i) x) := by
  rw [pairing_projector_product b p horth hcomplete hadjoint, Fintype.prod_sum_type]
  simp only [Sum.swap_inl, Sum.swap_inr]
  calc
    _ = (∏ i, b (p (Sum.inl i) x) (p (Sum.inr i) y)) *
        ∏ i, (b (p (Sum.inl i) y) (p (Sum.inr i) x))⁻¹ := by
      congr 1
      exact Finset.prod_congr rfl (fun i _ => hskew _ _)
    _ = _ := by simp only [div_eq_mul_inv, Finset.prod_mul_distrib]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitPairingFormula.Construction

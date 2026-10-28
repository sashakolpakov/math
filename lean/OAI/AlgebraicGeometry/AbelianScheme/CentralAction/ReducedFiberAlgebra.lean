import Mathlib

/-! # Reduced Fiber Algebra -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ReducedFiberAlgebra.Construction

noncomputable section

/-! A finite algebra with as many geometric points as its dimension is
the product of its residue-field points. This detects the absence of
nilpotents in the finite polarization fibers. -/

variable (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]

def algebraPointEvaluation : A →ₐ[k] ((A →ₐ[k] k) → k) := AlgHom.pi fun f => f

theorem algebraPointEvaluation_injective
    (hcard : Nat.card (A →ₐ[k] k) = Module.finrank k A) :
    Function.Injective (algebraPointEvaluation k A) := by
  let : Fintype (A →ₐ[k] k) := Fintype.ofFinite _
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (AlgHom.toLinearMap : (A →ₐ[k] k) → A →ₗ[k] k)
    (linearIndependent_algHom_toLinearMap k A k)
    (by simpa only [Fintype.card_eq_nat_card, Subspace.dual_finrank_eq] using hcard)
  intro x y hxy
  apply Module.eval_apply_injective k
  apply b.ext
  intro f
  simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
  change f x = f y
  exact congrFun hxy f

/-- The actual evaluation map is an algebra isomorphism, not just an
equality of point counts. It will be used on finite geometric fibers. -/
def algebraPointEvaluationEquiv
    (hcard : Nat.card (A →ₐ[k] k) = Module.finrank k A) :
    A ≃ₐ[k] ((A →ₐ[k] k) → k) := by
  let : Fintype (A →ₐ[k] k) := Fintype.ofFinite _
  have hd : Module.finrank k A = Module.finrank k ((A →ₐ[k] k) → k) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card, hcard]
  have hi := algebraPointEvaluation_injective k A hcard
  exact AlgEquiv.ofBijective (algebraPointEvaluation k A)
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (algebraPointEvaluation k A).toLinearMap) hd).mp hi⟩

theorem finite_algebra_etale_of_point_count
    (hcard : Nat.card (A →ₐ[k] k) = Module.finrank k A) : Algebra.Etale k A := by
  exact Algebra.Etale.of_equiv (algebraPointEvaluationEquiv k A hcard).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ReducedFiberAlgebra.Construction

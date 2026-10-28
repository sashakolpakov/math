import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Set

/-! # Rename Polynomial Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RenamePolynomialExtension

noncomputable section

/-! Renaming indices along an injection is a polynomial-ring
extension in the complementary indices, via an explicit algebra isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι κ : Type} (j : ι → κ) (hj : Function.Injective j)

def complement := {k : κ // k ∉ Set.range j}

def indices : complement j ⊕ ι ≃ κ := by
  classical
  exact ((Equiv.sumCongr (Equiv.refl (complement j)) (Equiv.ofInjective j hj)).trans
    (Equiv.sumComm (complement j) (Set.range j))).trans (Equiv.Set.sumCompl (Set.range j))

theorem indices_inr (i : ι) : indices j hj (Sum.inr i) = j i := rfl

theorem indices_symm (i : ι) : (indices j hj).symm (j i) = Sum.inr i :=
  (indices j hj).symm_apply_eq.mpr (indices_inr j hj i).symm

variable (R : Type) [CommRing R]

def equivalence : MvPolynomial κ R ≃ₐ[R] MvPolynomial (complement j) (MvPolynomial ι R) :=
  (MvPolynomial.renameEquiv R (indices j hj).symm).trans
    (MvPolynomial.sumAlgEquiv R (complement j) ι)

theorem equivalence_X (i : ι) : equivalence j hj R (MvPolynomial.X (j i)) = MvPolynomial.C (MvPolynomial.X i) := by
  change MvPolynomial.sumAlgEquiv R (complement j) ι
    (MvPolynomial.rename (indices j hj).symm (MvPolynomial.X (j i))) = _
  rw [MvPolynomial.rename_X, indices_symm, MvPolynomial.sumAlgEquiv_X_inr]

theorem equivalence_rename (p : MvPolynomial ι R) :
    equivalence j hj R (MvPolynomial.rename j p) = MvPolynomial.C p := by
  have he : (equivalence j hj R).toAlgHom.comp (MvPolynomial.rename j) =
      IsScalarTower.toAlgHom R (MvPolynomial ι R) (MvPolynomial (complement j) (MvPolynomial ι R)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, AlgEquiv.coe_toAlgHom]
    exact equivalence_X j hj R i
  exact DFunLike.congr_fun he p

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RenamePolynomialExtension

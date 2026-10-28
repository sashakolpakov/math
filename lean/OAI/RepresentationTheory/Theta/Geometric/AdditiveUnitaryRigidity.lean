import OAI.RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Additive Unitary Rigidity -/

namespace OAI.RepresentationTheory.Theta.Geometric.AdditiveUnitaryRigidity

noncomputable section

/-! Infinitesimal unitary automorphy is rigid: a holomorphic additive
comparison with purely imaginary periods has zero period character. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : AddSubgroup V) [CompactSpace (V ⧸ L)]

theorem additiveUnitaryAutomorphy_constant (f : V → ℂ) (χ : L → ℂ)
    (hχ : ∀ l, (χ l).re = 0) (hf : Differentiable ℂ f)
    (htrans : ∀ (l : L) z, f (z + l.val) = f z + χ l) (z w : V) : f z = f w := by
  have hnorm : ∀ (l : L) z, ‖Complex.exp (f (z + l.val))‖ = ‖Complex.exp (f z)‖ := by
    intro l z
    rw [htrans, Complex.norm_exp, Complex.norm_exp, Complex.add_re, hχ, add_zero]
  have heq : (fun z => Complex.exp (f z)) = fun _ => Complex.exp (f 0) :=
    funext (fun z => UnitaryAutomorphyRigidity.normPeriodic_holomorphic_constant L _ hnorm hf.cexp z 0)
  have hzero (x : V) : fderiv ℂ f x = 0 := by
    have H := (hf x).hasFDerivAt.cexp
    rw [heq] at H
    have H' : Complex.exp (f x) • fderiv ℂ f x = 0 := H.unique (hasFDerivAt_const _ _)
    exact (smul_eq_zero.mp H').resolve_left (Complex.exp_ne_zero _)
  exact is_const_of_fderiv_eq_zero hf hzero z w

theorem additiveUnitaryAutomorphy_trivial (f : V → ℂ) (χ : L → ℂ)
    (hχ : ∀ l, (χ l).re = 0) (hf : Differentiable ℂ f)
    (htrans : ∀ (l : L) z, f (z + l.val) = f z + χ l) (l : L) : χ l = 0 := by
  have H : f 0 + χ l = f 0 + 0 := (htrans l 0).symm.trans
    ((additiveUnitaryAutomorphy_constant L f χ hχ hf htrans _ _).trans (add_zero _).symm)
  exact add_left_cancel H

end

end OAI.RepresentationTheory.Theta.Geometric.AdditiveUnitaryRigidity

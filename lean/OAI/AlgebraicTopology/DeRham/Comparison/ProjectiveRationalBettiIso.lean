import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality

/-! # Projective Rational Betti Iso -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveRationalBettiIso.IntegralProjectiveVariety

noncomputable section

/-!
# Rational Betti transport under actual algebraic isomorphisms

Both directions are the ordinary singular-cohomology pullbacks of the given
algebraic isomorphism and its inverse. These formulas keep the transport used
in the rational cycle-class naturality square explicit.
-/

open _root_.CategoryTheory

variable {V W T : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- The actual rational singular-cohomology isomorphism, with both directions explicit. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso (e : V.toOver ≅ W.toOver) (n : ℕ) :
    W.rationalCohomology n ≅ V.rationalCohomology n where
  hom := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom n
  inv := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.inv n
  hom_inv_id := by
    rw [← AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_comp, e.inv_hom_id, AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_id]
  inv_hom_id := by
    rw [← AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_comp, e.hom_inv_id, AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_id]

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso_hom (e : V.toOver ≅ W.toOver) (n : ℕ) :
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso e n).hom = AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom n := rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso_inv (e : V.toOver ≅ W.toOver) (n : ℕ) :
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso e n).inv = AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.inv n := rfl

/-- The same concrete transport viewed as an equivalence of rational vector spaces. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv (e : V.toOver ≅ W.toOver) (n : ℕ) :
    W.rationalCohomology n ≃ₗ[ℚ] V.rationalCohomology n :=
  (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso e n).toLinearEquiv

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv_apply (e : V.toOver ≅ W.toOver) (n : ℕ)
    (a : W.rationalCohomology n) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv e n a = AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom n a := rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv_symm_apply (e : V.toOver ≅ W.toOver) (n : ℕ)
    (a : V.rationalCohomology n) :
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv e n).symm a = AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.inv n a := rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso_refl (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso (Iso.refl V.toOver) n = Iso.refl (V.rationalCohomology n) := by
  apply Iso.ext
  exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_id V n

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso_symm (e : V.toOver ≅ W.toOver) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso e.symm n = (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso e n).symm := rfl

/-- Composition follows the contravariant order of genuine cohomology pullback. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso_trans (e : V.toOver ≅ W.toOver)
    (f : W.toOver ≅ T.toOver) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso (e.trans f) n = AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso f n ≪≫ AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiIso e n := by
  apply Iso.ext
  exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_comp e.hom f.hom n

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_hom_inv_apply (e : V.toOver ≅ W.toOver) (n : ℕ)
    (a : V.rationalCohomology n) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom n (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.inv n a) = a :=
  (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv e n).apply_symm_apply a

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_inv_hom_apply (e : V.toOver ≅ W.toOver) (n : ℕ)
    (a : W.rationalCohomology n) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.inv n (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom n a) = a :=
  (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv e n).symm_apply_apply a

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveRationalBettiIso.IntegralProjectiveVariety

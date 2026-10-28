import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.TwistEulerZero
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GeneratedLineBundleFrames

/-! # Opposite Ample Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A nonzero line bundle on a nonempty projective scheme has a nonzero
ample-twist Euler polynomial. Two such polynomials have simultaneous
nonzero values at opposite positive and negative integers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

local instance OppositeAmpleEuler.ampleEulerClassCommGroup (X : Scheme.{u}) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Line.Bundles.LineBundle.isoClassCommGroup X

theorem OppositeAmpleEuler.polynomial_exists_opposite_nonzero_values
    (P Q : Polynomial ℚ) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ P.eval (m : ℚ) ≠ 0 ∧ Q.eval (-(m : ℚ)) ≠ 0 := by
  classical
  by_contra h
  have hprod : P * Q.comp (-Polynomial.X) = 0 := by
    apply HilbertConstruction.Polynomial.EventualGrid.polynomial_eq_of_positive_nat_evals
    intro m hm
    have hz : P.eval (m : ℚ) = 0 ∨ Q.eval (-(m : ℚ)) = 0 := by
      by_contra hn
      push Not at hn
      exact h ⟨m, hm, hn⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_X, Polynomial.eval_zero]
    exact mul_eq_zero.mpr hz
  rcases mul_eq_zero.mp hprod with hp | hq
  · exact hP hp
  · exact hQ (Polynomial.comp_neg_X_eq_zero_iff.mp hq)

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.exists_nonzero_integerEulerPolynomial
    {K : Type u} [Field K] {X : Scheme.{u}} [Nonempty X]
    (p : X ⟶ Spec (.of K)) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (M : Line.Bundles.LineBundle X) :
    ∃ P : Polynomial ℚ, P ≠ 0 ∧ ∀ z : ℤ,
      P.eval (z : ℚ) =
        (LineBundle.EulerShifts.lineBundleClassEuler p (Line.Bundles.LineBundle.classOf M * Line.Bundles.LineBundle.classOf L ^ z) : ℚ) := by
  obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial p L (Line.Bundles.LineBundle.classOf M)
  refine ⟨P, ?_, hP⟩
  intro hz
  have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
  have : M.sheaf.IsFiniteType := M.isFiniteType
  apply FormalGeometry.Completion.GeneratedLineBundleFrames.Construction.lineBundle_not_isZero M
  apply E.coherent_isZero_of_twist_euler_zero p M.sheaf
  intro m
  have hm := hP (m : ℤ)
  simp only [hz, Polynomial.eval_zero, zpow_natCast,
    ← Line.Bundles.LineBundle.classOf_tensorPower, ← Line.Bundles.LineBundle.classOf_tensor,
    LineBundle.EulerShifts.lineBundleClassEuler_classOf] at hm
  exact_mod_cast hm.symm

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.exists_opposite_nonzero_euler
    {K : Type u} [Field K] {X : Scheme.{u}} [Nonempty X]
    (p : X ⟶ Spec (.of K)) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (M N : Line.Bundles.LineBundle X) :
    ∃ m : ℕ, 0 < m ∧
      LineBundle.EulerShifts.lineBundleClassEuler p (Line.Bundles.LineBundle.classOf M * Line.Bundles.LineBundle.classOf L ^ (m : ℤ)) ≠ 0 ∧
      LineBundle.EulerShifts.lineBundleClassEuler p (Line.Bundles.LineBundle.classOf N * Line.Bundles.LineBundle.classOf L ^ (-(m : ℤ))) ≠ 0 := by
  obtain ⟨P, hP, eP⟩ := E.exists_nonzero_integerEulerPolynomial p M
  obtain ⟨Q, hQ, eQ⟩ := E.exists_nonzero_integerEulerPolynomial p N
  obtain ⟨m, hm, hp, hq⟩ := OppositeAmpleEuler.polynomial_exists_opposite_nonzero_values P Q hP hQ
  refine ⟨m, hm, ?_, ?_⟩
  · intro hz
    apply hp
    simpa only [Int.cast_natCast, hz, Int.cast_zero] using eP (m : ℤ)
  · intro hz
    apply hq
    simpa only [Int.cast_neg, Int.cast_natCast, hz, Int.cast_zero] using eQ (-(m : ℤ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteGeneration
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PositiveMultiplication
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupHomFlat
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialPositivity
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Polynomial.Div

/-! # Shift Isogeny -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.ShiftIsogeny

noncomputable section

/-! Integral endomorphisms have finite, surjective and flat sufficiently
large integer shifts. A monic annihilator supplies a composition factor
of a positive multiplication map. This applies to the actual geometric
Frobenius without a spectral or characteristic-polynomial hypothesis. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- Polynomial division constructs the actual composition factor. -/
theorem integral_shift_factor {R : Type*} [Ring R] (f : R)
    (Q : Polynomial ℤ) (hQ : Polynomial.aeval f Q = 0) (n : ℕ) :
    ∃ g : R, g * ((n : R) - f) = ↑(Q.eval (n : ℤ)) := by
  obtain ⟨H, hH⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := Q) (a := (n : ℤ))
  have he : Q - Polynomial.C (Q.eval (n : ℤ)) =
      H * (Polynomial.X - Polynomial.C (n : ℤ)) := by
    rw [hH, mul_comm]
  have ha := congrArg (Polynomial.aeval f) he
  simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    hQ, zero_sub, map_natCast] at ha
  refine ⟨Polynomial.aeval f H, ?_⟩
  calc
    _ = -(Polynomial.aeval f H * (f - (n : R))) := by rw [← mul_neg, neg_sub]
    _ = ↑(Q.eval (n : ℤ)) := by rw [← ha, neg_neg]; rfl

theorem monic_eventually_positive (Q : Polynomial ℤ) (hQ : Q.Monic) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → 0 < Q.eval (n : ℤ) := by
  obtain ⟨b, hb⟩ := AlgebraicGeometry.FormalGeometry.Completion.PolynomialPositivity.Construction.polynomial_eventually_nat_pos_of_leadingCoeff_pos
    (Q.map (Int.castRingHom ℚ)) (by rw [(hQ.map _).leadingCoeff]; exact zero_lt_one)
  refine ⟨b, fun n hn => ?_⟩
  have h := hb n hn
  rw [Polynomial.eval_natCast_map] at h
  change (0 : ℚ) < (Q.eval (n : ℤ) : ℤ) at h
  exact_mod_cast h

/-- An integral ring element has sufficiently large shifts dividing a
positive integer inside the original ring. -/
theorem integral_shift_eventually_positive_factor {R : Type*} [Ring R]
    (f : R) (hf : IsIntegral ℤ f) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ m : ℕ, 0 < m ∧ ∃ g : R, g * ((n : R) - f) = (m : R) := by
  obtain ⟨Q, hQ, hQf⟩ := hf
  obtain ⟨b, hb⟩ := monic_eventually_positive Q hQ
  refine ⟨b, fun n hn => ?_⟩
  have hp := hb n hn
  obtain ⟨g, hg⟩ := integral_shift_factor f Q hQf n
  refine ⟨(Q.eval (n : ℤ)).toNat, by omega, g, ?_⟩
  rw [hg, ← Int.cast_natCast ((Q.eval (n : ℤ)).toNat), Int.toNat_of_nonneg hp.le]

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem endomorphism_shift_eventually_isogeny (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      IsFinite ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left ∧
      Surjective ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left ∧
      Flat ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left := by
  let : Module.Finite ℤ (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :=
    Module.Finite.iff_addGroup_fg.mpr (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteGeneration.Construction.algebraicEnd_finiteGenerated A)
  obtain ⟨b, hb⟩ := integral_shift_eventually_positive_factor f (IsIntegral.of_finite ℤ f)
  refine ⟨b, fun n hn => ?_⟩
  obtain ⟨m, hm, g, hg⟩ := hb n hn
  let s := ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom
  let t := g.toMul.hom.hom
  have he : s.left ≫ t.left = ((𝟙 A : A ⟶ A) ^ m).left := by
    have h := congrArg (fun z : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A => z.toMul.hom.hom.left) hg
    change s.left ≫ t.left = (m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom.left at h
    rw [← nsmul_one m, AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.algebraicEnd_nsmul_hom] at h
    exact h
  have : IsProper t.left := by
    have : IsProper (t.left ≫ A.hom) := by rw [Over.w]; infer_instance
    exact IsProper.of_comp t.left A.hom
  have : IsFinite (s.left ≫ t.left) := by
    rw [he]
    exact AlgebraicGeometry.FormalGeometry.Completion.PositiveMultiplication.Construction.multiplication_positive_isFinite A m hm
  have : IsFinite s.left := IsFinite.of_comp s.left t.left
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := ⟨⟩
  have : Surjective s.left := ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism.Construction.surjective_finite_endomorphism_of_isIntegral s.left
  exact ⟨inferInstance, inferInstance, AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat s⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.ShiftIsogeny

import OAI.Geometry.ComplexBall.Generation

/-! # Curves -/

namespace OAI.Geometry.ComplexBall.Curves.ArithmeticQuotient

noncomputable section

/-! Every SL(3) matrix lies on a polynomial curve through the identity,
by scaling the parameters in a transvection factorization. -/

open scoped Classical _root_.Polynomial

lemma sl_map_transvection {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {i j : Fin 3} (hij : i ≠ j) (a : R) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij (f a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro k l
  change f (((1 : Matrix (Fin 3) (Fin 3) R) + Matrix.single i j a) k l) =
    ((1 : Matrix (Fin 3) (Fin 3) S) + Matrix.single i j (f a)) k l
  simp only [Matrix.add_apply, map_add]
  apply congrArg₂ (· + ·)
  · by_cases hkl : k = l <;> simp only [Matrix.one_apply, hkl, ite_true, ite_false, map_one, map_zero]
  · simp only [Matrix.single_apply]
    split_ifs <;> simp

variable {K : Type*} [Field K]

theorem sl3_exists_polynomial_curve (g : ArithmeticQuotientEquationsData.SL K) :
    ∃ A : ArithmeticQuotientEquationsData.SL K[X], Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom 0) A = 1 ∧
      Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom 1) A = g := by
  apply Generation.ArithmeticQuotient.sl3_transvection_induction _ _ _ g
  · intro i j hij a
    refine ⟨Matrix.SpecialLinearGroup.transvection hij (Polynomial.C a * Polynomial.X), ?_, ?_⟩
    · rw [sl_map_transvection]
      simp
    · rw [sl_map_transvection]
      simp
  · intro g h hg hh
    obtain ⟨A, hA0, hA1⟩ := hg
    obtain ⟨B, hB0, hB1⟩ := hh
    exact ⟨A * B, by rw [map_mul, hA0, hB0, one_mul], by rw [map_mul, hA1, hB1]⟩

end

end OAI.Geometry.ComplexBall.Curves.ArithmeticQuotient

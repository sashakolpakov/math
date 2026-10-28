import OAI.Geometry.ComplexBall.ArithmeticQuotientSplitUnitary

/-! # Real Quadratic -/

namespace OAI.Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient

noncomputable section

/-! A negative quadratic algebra over R is C, with an explicit inverse.
This supplies the actual real-place unitary group realization. -/

open scoped Classical QuadraticAlgebra

lemma imaginaryRoot_sq (d r : ℝ) (hr : r ^ 2 = -d) :
    ((r : ℂ) * Complex.I) ^ 2 = (d : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hr]
  simp

def realQuadraticHom (d r : ℝ) (hr : r ^ 2 = -d) : QuadraticAlgebra ℝ d 0 →ₐ[ℝ] ℂ :=
  QuadraticAlgebra.lift ⟨(r : ℂ) * Complex.I, by
    simpa [pow_two, Algebra.smul_def] using imaginaryRoot_sq d r hr⟩

lemma realQuadraticHom_apply (d r : ℝ) (hr : r ^ 2 = -d) (z : QuadraticAlgebra ℝ d 0) :
    realQuadraticHom d r hr z = (z.re : ℂ) + (z.im : ℂ) * ((r : ℂ) * Complex.I) := by
  simp [realQuadraticHom, QuadraticAlgebra.lift, Algebra.smul_def]

def realQuadraticInverse (d r : ℝ) (z : ℂ) : QuadraticAlgebra ℝ d 0 := ⟨z.re, z.im / r⟩

lemma realQuadratic_left_inverse (d r : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0)
    (z : QuadraticAlgebra ℝ d 0) :
    realQuadraticInverse d r (realQuadraticHom d r hr z) = z := by
  rw [realQuadraticHom_apply]
  apply QuadraticAlgebra.ext <;> simp [realQuadraticInverse, hr0]

lemma realQuadratic_right_inverse (d r : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0) (z : ℂ) :
    realQuadraticHom d r hr (realQuadraticInverse d r z) = z := by
  rw [realQuadraticHom_apply]
  apply Complex.ext <;> simp [realQuadraticInverse, hr0]

def realQuadraticEquiv (d r : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0) :
    QuadraticAlgebra ℝ d 0 ≃+* ℂ :=
  RingEquiv.ofBijective (realQuadraticHom d r hr).toRingHom
    ⟨Function.LeftInverse.injective (realQuadratic_left_inverse d r hr hr0),
      Function.RightInverse.surjective (realQuadratic_right_inverse d r hr hr0)⟩

lemma realQuadraticEquiv_star (d r : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0)
    (z : QuadraticAlgebra ℝ d 0) :
    realQuadraticEquiv d r hr hr0 (star z) = star (realQuadraticEquiv d r hr hr0 z) := by
  change realQuadraticHom d r hr (star z) = star (realQuadraticHom d r hr z)
  rw [realQuadraticHom_apply, realQuadraticHom_apply]
  apply Complex.ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

lemma realQuadraticEquiv_scalar (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0) :
    realQuadraticEquiv d r hr hr0 (algebraMap ℝ (QuadraticAlgebra ℝ d 0) b) = (b : ℂ) :=
  (realQuadraticHom d r hr).commutes b

def realQuadraticUnitaryEquiv (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0) :
    ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra ℝ d 0)) (algebraMap ℝ _ b) ≃* ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ) :=
  (ArithmeticQuotientSplitUnitary.unitaryEquiv _ _ _ (realQuadraticEquiv d r hr hr0)
    (realQuadraticEquiv_star d r hr hr0)).trans
      (ArithmeticQuotientSplitUnitary.unitaryCoefficientEquiv _ _ (b : ℂ) (realQuadraticEquiv_scalar d r b hr hr0))

lemma realQuadraticUnitaryEquiv_entry (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra ℝ d 0)) (algebraMap ℝ _ b)) (i j : Fin 3) :
    (realQuadraticUnitaryEquiv d r b hr hr0 g).val i j = realQuadraticHom d r hr (g.val i j) := rfl

lemma realQuadraticUnitaryEquiv_symm_entry (d r b : ℝ) (hr : r ^ 2 = -d) (hr0 : r ≠ 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (b : ℂ)) (i j : Fin 3) :
    ((realQuadraticUnitaryEquiv d r b hr hr0).symm g).val i j =
      realQuadraticInverse d r (g.val i j) := by
  let e := realQuadraticUnitaryEquiv d r b hr hr0
  have he := realQuadraticUnitaryEquiv_entry d r b hr hr0 (e.symm g) i j
  change (e (e.symm g)).val i j = _ at he
  rw [e.apply_symm_apply] at he
  rw [he]
  exact (realQuadratic_left_inverse d r hr hr0 _).symm

end

end OAI.Geometry.ComplexBall.RealQuadratic.ArithmeticQuotient

import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrder

/-! # Polynomial Translation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation.Construction

noncomputable section

/-! Transport of polynomial order and derivatives from a point to the origin. -/

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Translation sends a polynomial `p(X)` to `p(X + a)`. -/
def polynomialTranslate (a : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i => X i + C (a i))

@[simp]
theorem polynomialTranslate_X (a : σ → R) (i : σ) :
    polynomialTranslate a (X i) = X i + C (a i) := aeval_X _ _

@[simp]
theorem polynomialTranslate_C (a : σ → R) (r : R) :
    polynomialTranslate a (C r) = C r := aeval_C _ _

theorem polynomialTranslate_add (a b : σ → R) :
    (polynomialTranslate a).comp (polynomialTranslate b) = polynomialTranslate (a + b) := by
  ext i
  simp [add_assoc]

@[simp]
theorem polynomialTranslate_zero : polynomialTranslate (0 : σ → R) = AlgHom.id R _ := by
  ext i
  simp

/-- Translation is an algebra automorphism, with inverse translation by `-a`. -/
def polynomialTranslationEquiv (a : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (polynomialTranslate a) (polynomialTranslate (-a))
    (by rw [polynomialTranslate_add, add_neg_cancel, polynomialTranslate_zero])
    (by rw [polynomialTranslate_add, neg_add_cancel, polynomialTranslate_zero])

/-- Formal partial derivatives commute with translations. -/
theorem polynomialTranslate_pderiv (a : σ → R) (i : σ) (p : MvPolynomial σ R) :
    polynomialTranslate a (pderiv i p) = pderiv i (polynomialTranslate a p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases hji : j = i
    · subst j
      simp [hp, map_add]
    · simp [hp, map_add, pderiv_X_of_ne hji]

/-- The constant coefficient after translation is evaluation at the translating point. -/
theorem constantCoeff_polynomialTranslate (a : σ → R) (p : MvPolynomial σ R) :
    constantCoeff (polynomialTranslate a p) = eval a p := by
  have he : (constantCoeff : MvPolynomial σ R →+* R).comp
      (polynomialTranslate a).toRingHom = eval a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp
  exact DFunLike.congr_fun he p

/-- The ideal of polynomials vanishing at a specified point. -/
def polynomialPointIdeal (a : σ → R) : Ideal (MvPolynomial σ R) := RingHom.ker (eval a)

theorem polynomialPointIdeal_eq_comap (a : σ → R) :
    polynomialPointIdeal a =
      (idealOfVars σ R).comap (polynomialTranslate a).toRingHom := by
  ext p
  change eval a p = 0 ↔ polynomialTranslate a p ∈ idealOfVars σ R
  rw [DifferentialOrder.Construction.mem_idealOfVars_iff_constantCoeff_eq_zero, constantCoeff_polynomialTranslate]

theorem polynomialPointIdeal_map_translate (a : σ → R) :
    (polynomialPointIdeal a).map (polynomialTranslate a).toRingHom = idealOfVars σ R := by
  rw [polynomialPointIdeal_eq_comap]
  exact Ideal.map_comap_of_surjective _ (polynomialTranslationEquiv a).surjective _

/-- Translation identifies the powers of the point ideal with the powers
of the ideal of variables at the origin. -/
theorem polynomialTranslate_mem_vars_pow_iff (a : σ → R) (p : MvPolynomial σ R) (n : ℕ) :
    polynomialTranslate a p ∈ idealOfVars σ R ^ n ↔ p ∈ polynomialPointIdeal a ^ n := by
  have hmap : (polynomialPointIdeal a ^ n).map (polynomialTranslate a).toRingHom =
      idealOfVars σ R ^ n := by
    rw [Ideal.map_pow, polynomialPointIdeal_map_translate]
  rw [← hmap, Ideal.mem_map_iff_of_surjective (polynomialTranslate a).toRingHom
    (polynomialTranslationEquiv a).surjective]
  constructor
  · rintro ⟨q, hq, he⟩
    have hqp : q = p := (polynomialTranslationEquiv a).injective he
    exact hqp ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- Iterated partial derivatives also commute with translations. -/
theorem polynomialTranslate_iteratedPDeriv (a : σ → R) (l : List σ) (p : MvPolynomial σ R) :
    polynomialTranslate a (DifferentialOrder.Construction.iteratedPDeriv l p) = DifferentialOrder.Construction.iteratedPDeriv l (polynomialTranslate a p) := by
  induction l generalizing p with
  | nil => rfl
  | cons i l ih =>
    change polynomialTranslate a (DifferentialOrder.Construction.iteratedPDeriv l (pderiv i p)) =
      DifferentialOrder.Construction.iteratedPDeriv l (pderiv i (polynomialTranslate a p))
    rw [ih, polynomialTranslate_pderiv]

/-- At any rational point in characteristic zero, a polynomial of finite
positive order supplies a derivative equation vanishing there with nonzero gradient. -/
theorem polynomial_atPoint_derivative_with_nonzero_gradient
    {K : Type*} [Field K] [CharZero K] (a : σ → K) (n : ℕ) {p : MvPolynomial σ K}
    (hp : p ∈ polynomialPointIdeal a ^ (n + 1))
    (hp1 : p ∉ polynomialPointIdeal a ^ (n + 2)) :
    ∃ (l : List σ) (i : σ), l.length = n ∧ eval a (DifferentialOrder.Construction.iteratedPDeriv l p) = 0 ∧
      eval a (pderiv i (DifferentialOrder.Construction.iteratedPDeriv l p)) ≠ 0 := by
  have htranslated := (polynomialTranslate_mem_vars_pow_iff a p (n + 1)).mpr hp
  have htranslated1 : polynomialTranslate a p ∉ idealOfVars σ K ^ (n + 2) :=
    fun h => hp1 ((polynomialTranslate_mem_vars_pow_iff a p (n + 2)).mp h)
  obtain ⟨l, i, hl, hz, hi⟩ :=
    DifferentialOrder.Construction.polynomial_exists_derivative_with_nonzero_gradient n htranslated htranslated1
  rw [← polynomialTranslate_iteratedPDeriv, constantCoeff_polynomialTranslate] at hz
  rw [← polynomialTranslate_iteratedPDeriv, ← polynomialTranslate_pderiv,
    constantCoeff_polynomialTranslate] at hi
  exact ⟨l, i, hl, hz, hi⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation.Construction

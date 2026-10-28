import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData
import OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

/-! # Arithmetic Quotient Split Unitary -/

namespace OAI.Geometry.ComplexBall.ArithmeticQuotientSplitUnitary

noncomputable section

section

/-! The actual unitary algebraic group in Lattices's repaired polynomial API.
Every point group is the verified six-dimensional matrix image, and the
membership equivalence is proved by evaluation of the explicit equations.
Geometric connectedness and semisimplicity are separate obligations. -/

open scoped Classical

variable {k : Type} [Field k]

def unitaryAlgebraicGroup (d b : k) : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k 6 where
  equations := Set.range (ArithmeticQuotientEquationsData.unitaryPolynomial d b)
  subgroup K _ f := ArithmeticQuotientEquationsData.sixDimensionalUnitary (f d) (f b)
  mem_iff K _ f M := by
    change M ∈ ArithmeticQuotientEquationsData.sixDimensionalUnitary (f d) (f b) ↔
      ∀ p ∈ Set.range (ArithmeticQuotientEquationsData.unitaryPolynomial d b),
        MvPolynomial.eval₂Hom f (fun ij => M.val ij.1 ij.2) p = 0
    constructor
    · intro h p hp
      obtain ⟨e, rfl⟩ := hp
      rw [ArithmeticQuotientEquationsData.unitaryPolynomial_eval]
      exact (ArithmeticQuotientEquationsData.unitaryEquation_zero_iff (f d) (f b) M).mpr h e
    · intro h
      apply (ArithmeticQuotientEquationsData.unitaryEquation_zero_iff (f d) (f b) M).mp
      intro e
      rw [← ArithmeticQuotientEquationsData.unitaryPolynomial_eval d b f M.val e]
      exact h _ ⟨e, rfl⟩

def regularUnitaryPoints (d b : k) :
    ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra k d 0)) (algebraMap k _ b) →*
      (unitaryAlgebraicGroup d b).RationalPoints where
  toFun g := ⟨ArithmeticQuotientEquationsData.regularSpecialLinear d g.val, ⟨g.val, g.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (ArithmeticQuotientEquationsData.regularSpecialLinear d))
  map_mul' g h := Subtype.ext (map_mul (ArithmeticQuotientEquationsData.regularSpecialLinear d) g.val h.val)

theorem regularUnitaryPoints_bijective (d b : k) :
    Function.Bijective (regularUnitaryPoints d b) := by
  constructor
  · intro g h he
    apply Subtype.ext
    exact ArithmeticQuotientEquationsData.regularSpecialLinear_injective d (congrArg Subtype.val he)
  · intro g
    obtain ⟨A, hA, hM⟩ := g.property
    refine ⟨⟨A, hA⟩, ?_⟩
    exact Subtype.ext hM

/-- A proved identification of the unitary matrices with rational points. -/
def regularUnitaryEquiv (d b : k) :
    ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra k d 0)) (algebraMap k _ b) ≃*
      (unitaryAlgebraicGroup d b).RationalPoints :=
  MulEquiv.ofBijective (regularUnitaryPoints d b) (regularUnitaryPoints_bijective d b)

end

section

/-! Identification of the polynomial model with the original CM-field
unitary group. The quadratic presentation and conjugation compatibility
are proved, and no point-realization hypothesis is introduced. -/

open scoped Classical QuadraticAlgebra
open _root_.NumberField

section Equiv
variable {K L : Type*} [CommRing K] [CommRing L]

/-- Changing a proved-equal coefficient leaves every matrix entry unchanged. -/
def unitaryCoefficientEquiv (c : K →+* K) (b b' : K) (h : b = b') : ArithmeticQuotientEquationsData.SU c b ≃* ArithmeticQuotientEquationsData.SU c b' where
  toFun g := ⟨g.val, h ▸ g.property⟩
  invFun g := ⟨g.val, h.symm ▸ g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def unitaryEquiv (c : K →+* K) (d : L →+* L) (b : K) (e : K ≃+* L)
    (hc : ∀ x : K, e (c x) = d (e x)) : ArithmeticQuotientEquationsData.SU c b ≃* ArithmeticQuotientEquationsData.SU d (e b) :=
  MulEquiv.ofBijective (ArithmeticQuotientEquationsData.unitaryMap c d b e.toRingHom hc) ⟨by
    intro g h he
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply e.injective
    exact congrArg (fun z : ArithmeticQuotientEquationsData.SU d (e b) => z.val i j) he,
    by
      intro g
      have hd (x : L) : e.symm (d x) = c (e.symm x) := by
        apply e.injective
        rw [e.apply_symm_apply, hc, e.apply_symm_apply]
      let A : ArithmeticQuotientEquationsData.SL K := Matrix.SpecialLinearGroup.map e.symm.toRingHom g.val
      have hA : A ∈ ArithmeticQuotientEquationsData.unitarySubgroup c b := by
        have h := (ArithmeticQuotientEquationsData.unitaryMap d c (e b) e.symm.toRingHom hd g).property
        change A ∈ ArithmeticQuotientEquationsData.unitarySubgroup c (e.symm (e b)) at h
        simpa only [RingEquiv.symm_apply_apply] using h
      refine ⟨⟨A, hA⟩, ?_⟩
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      exact e.apply_symm_apply (g.val i j)⟩

end Equiv

section CM
variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

lemma quadraticEquiv_star (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (z : QuadraticAlgebra (ArithmeticQuotientEquationsData.RealField E) (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) 0) :
    ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 (star z) =
      IsCMField.complexConj E (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 z) := by
  change ArithmeticQuotientEquationsData.quadraticLift δ hδ (star z) = IsCMField.complexConj E (ArithmeticQuotientEquationsData.quadraticLift δ hδ z)
  rw [ArithmeticQuotientEquationsData.quadraticLift_conjugate, ArithmeticQuotientEquationsData.quadraticLift_apply]
  simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sub_eq_add_neg]

def realCoefficient (b : E) (hb : IsCMField.complexConj E b = b) : ArithmeticQuotientEquationsData.RealField E :=
  ⟨b, (IsCMField.complexConj_eq_self_iff E b).mp hb⟩

def rationalQuadraticUnitaryEquiv (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra (ArithmeticQuotientEquationsData.RealField E) (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) 0))
      (algebraMap (ArithmeticQuotientEquationsData.RealField E) _ (realCoefficient b hb)) ≃* ArithmeticQuotientEquationsData.RationalSU b := by
  let e := ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0
  have hc : e (algebraMap (ArithmeticQuotientEquationsData.RealField E) _ (realCoefficient b hb)) = b :=
    e.commutes (realCoefficient b hb)
  have he := unitaryEquiv
    (starRingEnd (QuadraticAlgebra (ArithmeticQuotientEquationsData.RealField E) (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) 0))
    (IsCMField.complexConj E).toRingHom
    (algebraMap (ArithmeticQuotientEquationsData.RealField E) _ (realCoefficient b hb)) e.toRingEquiv
    (fun z => by simpa [e, starRingEnd_apply] using quadraticEquiv_star δ hδ hδ0 z)
  have hc' : e.toRingEquiv (algebraMap (ArithmeticQuotientEquationsData.RealField E) _ (realCoefficient b hb)) = b := by
    simpa only [AlgEquiv.coe_ringEquiv] using hc
  exact he.trans (unitaryCoefficientEquiv _ _ b hc')

end CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def originalUnitaryAlgebraicGroup (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) :
    NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup (ArithmeticQuotientEquationsData.RealField E) 6 :=
  unitaryAlgebraicGroup (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) (realCoefficient b hb)

/-- The original E-matrices are the rational points of the constructed
algebraic group over F = E⁺. -/
def originalUnitaryRationalEquiv (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    ArithmeticQuotientEquationsData.RationalSU b ≃* (originalUnitaryAlgebraicGroup b hb δ hδ).RationalPoints :=
  (rationalQuadraticUnitaryEquiv b hb δ hδ hδ0).symm.trans
    (regularUnitaryEquiv (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) (realCoefficient b hb))

end

section

/-! Splitting the quadratic algebra over a field containing a nonzero square
root of d. This is the first step in identifying the geometric unitary group
with SL(3), with conjugation becoming exchange of the two factors. -/

open scoped Classical QuadraticAlgebra

variable {K : Type*} [Field K] [CharZero K]

def splitQuadraticHom (d r : K) (hr : r ^ 2 = d) : QuadraticAlgebra K d 0 →+* K × K :=
  ((QuadraticAlgebra.lift ⟨r, by simpa [pow_two, Algebra.smul_def] using hr⟩ :
      QuadraticAlgebra K d 0 →ₐ[K] K).toRingHom).prod
    ((QuadraticAlgebra.lift ⟨-r, by simpa [pow_two, Algebra.smul_def] using hr⟩ :
      QuadraticAlgebra K d 0 →ₐ[K] K).toRingHom)

omit [CharZero K] in
lemma splitQuadraticHom_apply (d r : K) (hr : r ^ 2 = d) (z : QuadraticAlgebra K d 0) :
    splitQuadraticHom d r hr z = (z.re + z.im * r, z.re - z.im * r) := by
  apply Prod.ext <;> simp [splitQuadraticHom, QuadraticAlgebra.lift,
    sub_eq_add_neg]

def splitQuadraticInverse (d r : K) (z : K × K) : QuadraticAlgebra K d 0 :=
  ⟨(z.1 + z.2) / 2, (z.1 - z.2) / (2 * r)⟩

lemma splitQuadratic_left_inverse (d r : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (z : QuadraticAlgebra K d 0) :
    splitQuadraticInverse d r (splitQuadraticHom d r hr z) = z := by
  rw [splitQuadraticHom_apply]
  apply QuadraticAlgebra.ext
  · change (z.re + z.im * r + (z.re - z.im * r)) / 2 = z.re
    field_simp
    ring
  · change (z.re + z.im * r - (z.re - z.im * r)) / (2 * r) = z.im
    field_simp
    ring

lemma splitQuadratic_right_inverse (d r : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (z : K × K) :
    splitQuadraticHom d r hr (splitQuadraticInverse d r z) = z := by
  rw [splitQuadraticHom_apply]
  apply Prod.ext
  · change (z.1 + z.2) / 2 + ((z.1 - z.2) / (2 * r)) * r = z.1
    field_simp
    ring
  · change (z.1 + z.2) / 2 - ((z.1 - z.2) / (2 * r)) * r = z.2
    field_simp
    ring

def splitQuadraticEquiv (d r : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0) :
    QuadraticAlgebra K d 0 ≃+* K × K :=
  RingEquiv.ofBijective (splitQuadraticHom d r hr)
    ⟨Function.LeftInverse.injective (splitQuadratic_left_inverse d r hr hr0),
      Function.RightInverse.surjective (splitQuadratic_right_inverse d r hr hr0)⟩

lemma splitQuadraticEquiv_star (d r : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (z : QuadraticAlgebra K d 0) :
    splitQuadraticEquiv d r hr hr0 (star z) = Prod.swap (splitQuadraticEquiv d r hr hr0 z) := by
  change splitQuadraticHom d r hr (star z) = Prod.swap (splitQuadraticHom d r hr z)
  rw [splitQuadraticHom_apply, splitQuadraticHom_apply]
  apply Prod.ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sub_eq_add_neg]

lemma splitQuadraticEquiv_scalar (d r b : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0) :
    splitQuadraticEquiv d r hr hr0 (algebraMap K (QuadraticAlgebra K d 0) b) = (b, b) := by
  change splitQuadraticHom d r hr _ = _
  rw [splitQuadraticHom_apply]
  simp

def splitUnitaryEquiv (d r b : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0) :
    ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra K d 0)) (algebraMap K _ b) ≃*
      ArithmeticQuotientEquationsData.SU (RingEquiv.prodComm : K × K ≃+* K × K).toRingHom (b, b) := by
  have h := unitaryEquiv (starRingEnd (QuadraticAlgebra K d 0))
    (RingEquiv.prodComm : K × K ≃+* K × K).toRingHom (algebraMap K _ b)
    (splitQuadraticEquiv d r hr hr0)
    (fun z => by simpa [starRingEnd_apply] using splitQuadraticEquiv_star d r hr hr0 z)
  exact h.trans (unitaryCoefficientEquiv _ _ (b, b)
    (splitQuadraticEquiv_scalar d r b hr hr0))

end

section

/-! The split unitary group is SL(3): the first component determines the
second by inverse transpose relative to the diagonal form. -/

open scoped Classical BigOperators
open _root_.Matrix
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

variable {K : Type*} [Field K]

abbrev swapInvolution : K × K →+* K × K :=
  (RingEquiv.prodComm : K × K ≃+* K × K).toRingHom

lemma swapInvolution_apply (z : K × K) : swapInvolution z = (z.2, z.1) := rfl

def formMatrix (b : K) : ArithmeticQuotientEquationsData.Mat K := Matrix.diagonal (ArithmeticQuotientEquationsData.diagonalCoefficient b)

lemma formMatrix_transpose (b : K) : (formMatrix b).transpose = formMatrix b :=
  Matrix.diagonal_transpose _

lemma formMatrix_mul_inverse (b : K) (hb : b ≠ 0) :
    formMatrix b * formMatrix b⁻¹ = 1 := by
  rw [formMatrix, formMatrix, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i = 2 <;> simp [ArithmeticQuotientEquationsData.diagonalCoefficient, hb, hi]
  · simp [h]

lemma formMatrix_inverse_mul (b : K) (hb : b ≠ 0) :
    formMatrix b⁻¹ * formMatrix b = 1 := by
  simpa only [inv_inv] using formMatrix_mul_inverse b⁻¹ (inv_ne_zero hb)

def dualMatrix (b : K) (A : ArithmeticQuotientEquationsData.SL K) : ArithmeticQuotientEquationsData.Mat K :=
  formMatrix b⁻¹ * (A⁻¹ : ArithmeticQuotientEquationsData.SL K).val.transpose * formMatrix b

lemma dualMatrix_det (b : K) (hb : b ≠ 0) (A : ArithmeticQuotientEquationsData.SL K) :
    (dualMatrix b A).det = 1 := by
  have hi := congrArg Matrix.det (formMatrix_inverse_mul b hb)
  simpa only [dualMatrix, det_mul, det_transpose, (A⁻¹ : ArithmeticQuotientEquationsData.SL K).property,
    mul_one, det_one] using hi

lemma dualMatrix_preserves (b : K) (hb : b ≠ 0) (A : ArithmeticQuotientEquationsData.SL K) :
    A.val.transpose * formMatrix b * dualMatrix b A = formMatrix b := by
  calc
    _ = (A.val.transpose * (formMatrix b * formMatrix b⁻¹) *
      (A⁻¹ : ArithmeticQuotientEquationsData.SL K).val.transpose) * formMatrix b := by
        dsimp [dualMatrix]
        noncomm_ring
    _ = formMatrix b := by
      rw [formMatrix_mul_inverse b hb, mul_one, ← Matrix.transpose_mul]
      change ((↑(A⁻¹ * A) : ArithmeticQuotientEquationsData.Mat K).transpose) * formMatrix b = _
      rw [inv_mul_cancel]
      simp

lemma dualMatrix_unique (b : K) (hb : b ≠ 0) (A : ArithmeticQuotientEquationsData.SL K) (B : ArithmeticQuotientEquationsData.Mat K)
    (h : A.val.transpose * formMatrix b * B = formMatrix b) : B = dualMatrix b A := by
  have he := congrArg (fun M : ArithmeticQuotientEquationsData.Mat K =>
    formMatrix b⁻¹ * (A⁻¹ : ArithmeticQuotientEquationsData.SL K).val.transpose * M) h
  have hi : (A⁻¹ : ArithmeticQuotientEquationsData.SL K).val.transpose * A.val.transpose = 1 := by
    rw [← Matrix.transpose_mul]
    change (↑(A * A⁻¹) : ArithmeticQuotientEquationsData.Mat K).transpose = 1
    simp
  calc
    B = (formMatrix b⁻¹ * ((A⁻¹ : ArithmeticQuotientEquationsData.SL K).val.transpose * A.val.transpose) *
      formMatrix b) * B := by rw [hi, mul_one, formMatrix_inverse_mul b hb, one_mul]
    _ = dualMatrix b A := by
      change _ = formMatrix b⁻¹ * (A⁻¹ : ArithmeticQuotientEquationsData.SL K).val.transpose * formMatrix b
      rw [← he]
      noncomm_ring

def pairSL (A B : ArithmeticQuotientEquationsData.SL K) : ArithmeticQuotientEquationsData.SL (K × K) :=
  ⟨fun i j => (A.val i j, B.val i j), by
    apply Prod.ext
    · exact ((RingHom.fst K K).map_det
        (fun i j : Fin 3 => (A.val i j, B.val i j))).trans A.property
    · exact ((RingHom.snd K K).map_det
        (fun i j : Fin 3 => (A.val i j, B.val i j))).trans B.property⟩

lemma swapUnitary_iff (b : K) (g : ArithmeticQuotientEquationsData.SL (K × K)) :
    g ∈ ArithmeticQuotientEquationsData.unitarySubgroup swapInvolution (b, b) ↔
      (g.val.map Prod.fst).transpose * formMatrix b * g.val.map Prod.snd = formMatrix b := by
  rw [ArithmeticQuotientEquationsData.unitary_iff_columns]
  have entry (A B : ArithmeticQuotientEquationsData.Mat K) (i j : Fin 3) :
      (A.transpose * formMatrix b * B) i j =
        ∑ k, ArithmeticQuotientEquationsData.diagonalCoefficient b k * A k i * B k j := by
    change (A.transpose * Matrix.diagonal (ArithmeticQuotientEquationsData.diagonalCoefficient b) * B) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    have he := congrArg Prod.fst (h i j)
    rw [entry]
    simpa only [ArithmeticQuotientEquationsData.diagonalCoefficient, formMatrix, Matrix.diagonal_apply,
      Prod.fst_sum, Prod.fst_mul, swapInvolution_apply,
      Matrix.map_apply, Prod.fst_zero, Prod.fst_one, apply_ite] using he
  · intro h i j
    have h' := congrArg Matrix.transpose h
    simp only [Matrix.transpose_mul, formMatrix_transpose, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at h'
    apply Prod.ext
    · have he := congrArg (fun M : ArithmeticQuotientEquationsData.Mat K => M i j) h
      rw [entry] at he
      simpa only [ArithmeticQuotientEquationsData.diagonalCoefficient, formMatrix, Matrix.diagonal_apply,
        Prod.fst_sum, Prod.fst_mul, swapInvolution_apply,
        Matrix.map_apply, Prod.fst_zero, Prod.fst_one, apply_ite] using he
    · have he := congrArg (fun M : ArithmeticQuotientEquationsData.Mat K => M i j) h'
      rw [entry] at he
      simpa only [ArithmeticQuotientEquationsData.diagonalCoefficient, formMatrix, Matrix.diagonal_apply,
        Prod.snd_sum, Prod.snd_mul, swapInvolution_apply,
        Matrix.map_apply, Prod.snd_zero, Prod.snd_one, apply_ite] using he

def swapUnitaryToSL (b : K) : ArithmeticQuotientEquationsData.SU (swapInvolution (K := K)) (b, b) →* ArithmeticQuotientEquationsData.SL K :=
  { toFun := fun g => Matrix.SpecialLinearGroup.map (RingHom.fst K K) g.val
    map_one' := map_one _
    map_mul' := fun g h => map_mul _ g.val h.val }

lemma swapUnitaryToSL_injective (b : K) (hb : b ≠ 0) :
    Function.Injective (swapUnitaryToSL b) := by
  intro g h he
  have hg := (swapUnitary_iff b g.val).mp g.property
  have hh := (swapUnitary_iff b h.val).mp h.property
  have hgf : g.val.val.map Prod.fst = h.val.val.map Prod.fst :=
    congrArg Subtype.val he
  have hgs : g.val.val.map Prod.snd = h.val.val.map Prod.snd := by
    rw [dualMatrix_unique b hb (swapUnitaryToSL b g) _ hg,
      dualMatrix_unique b hb (swapUnitaryToSL b h) _ hh, he]
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact Prod.ext (congrArg (fun M : ArithmeticQuotientEquationsData.Mat K => M i j) hgf)
    (congrArg (fun M : ArithmeticQuotientEquationsData.Mat K => M i j) hgs)

lemma swapUnitaryToSL_surjective (b : K) (hb : b ≠ 0) :
    Function.Surjective (swapUnitaryToSL b) := by
  intro A
  let B : ArithmeticQuotientEquationsData.SL K := ⟨dualMatrix b A, dualMatrix_det b hb A⟩
  let g := pairSL A B
  have hg : g ∈ ArithmeticQuotientEquationsData.unitarySubgroup swapInvolution (b, b) := by
    rw [swapUnitary_iff]
    exact dualMatrix_preserves b hb A
  exact ⟨⟨g, hg⟩, rfl⟩

def swapUnitaryEquivSL (b : K) (hb : b ≠ 0) : ArithmeticQuotientEquationsData.SU (swapInvolution (K := K)) (b, b) ≃* ArithmeticQuotientEquationsData.SL K :=
  MulEquiv.ofBijective (swapUnitaryToSL b)
    ⟨swapUnitaryToSL_injective b hb, swapUnitaryToSL_surjective b hb⟩

def quadraticUnitaryEquivSL [CharZero K] (d r b : K)
    (hr : r ^ 2 = d) (hr0 : r ≠ 0) (hb : b ≠ 0) :
    ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra K d 0)) (algebraMap K _ b) ≃* ArithmeticQuotientEquationsData.SL K :=
  (splitUnitaryEquiv d r b hr hr0).trans (swapUnitaryEquivSL b hb)

end

section

/-! Coordinate formulas for the inverse of the split unitary isomorphism.
They are polynomial in an SL matrix and its adjugate. -/

open scoped Classical QuadraticAlgebra
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

variable {K : Type*} [Field K] [CharZero K]

lemma splitUnitaryEquiv_entry (d r b : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra K d 0)) (algebraMap K _ b)) (i j : Fin 3) :
    (splitUnitaryEquiv d r b hr hr0 g).val i j = splitQuadraticHom d r hr (g.val i j) := rfl

lemma quadraticUnitaryEquivSL_fst (d r b : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (hb : b ≠ 0) (g : ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra K d 0)) (algebraMap K _ b))
    (i j : Fin 3) :
    (quadraticUnitaryEquivSL d r b hr hr0 hb g).val i j =
      (splitQuadraticHom d r hr (g.val i j)).1 := by
  exact congrArg Prod.fst (splitUnitaryEquiv_entry d r b hr hr0 g i j)

lemma quadraticUnitaryEquivSL_snd (d r b : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (hb : b ≠ 0) (g : ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra K d 0)) (algebraMap K _ b))
    (i j : Fin 3) :
    dualMatrix b (quadraticUnitaryEquivSL d r b hr hr0 hb g) i j =
      (splitQuadraticHom d r hr (g.val i j)).2 := by
  let s := splitUnitaryEquiv d r b hr hr0 g
  have hs := (swapUnitary_iff b s.val).mp s.property
  have he := dualMatrix_unique b hb (swapUnitaryToSL b s) _ hs
  calc
    _ = (s.val i j).2 := congrArg (fun M : ArithmeticQuotientEquationsData.Mat K => M i j) he.symm
    _ = _ := congrArg Prod.snd (splitUnitaryEquiv_entry d r b hr hr0 g i j)

lemma quadraticUnitaryEquivSL_symm_entry (d r b : K) (hr : r ^ 2 = d)
    (hr0 : r ≠ 0) (hb : b ≠ 0) (A : ArithmeticQuotientEquationsData.SL K) (i j : Fin 3) :
    ((quadraticUnitaryEquivSL d r b hr hr0 hb).symm A).val i j =
      splitQuadraticInverse d r (A.val i j, dualMatrix b A i j) := by
  let e := quadraticUnitaryEquivSL d r b hr hr0 hb
  have hf := quadraticUnitaryEquivSL_fst d r b hr hr0 hb (e.symm A) i j
  have hs := quadraticUnitaryEquivSL_snd d r b hr hr0 hb (e.symm A) i j
  change (e (e.symm A)).val i j = _ at hf
  change dualMatrix b (e (e.symm A)) i j = _ at hs
  rw [e.apply_symm_apply] at hf hs
  have he : splitQuadraticHom d r hr ((e.symm A).val i j) =
      (A.val i j, dualMatrix b A i j) := Prod.ext hf.symm hs.symm
  rw [← he]
  exact (splitQuadratic_left_inverse d r hr hr0 _).symm

end

/-! Polynomial coordinates for the inverse splitting map, with all divisions
absorbed into fixed scalar coefficients. -/

open scoped Classical
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

section Ring
variable {R S : Type*} [CommRing R] [CommRing S]

def splitDualMatrix (b binv : R) (A : ArithmeticQuotientEquationsData.Mat R) : ArithmeticQuotientEquationsData.Mat R :=
  Matrix.diagonal (ArithmeticQuotientEquationsData.diagonalCoefficient binv) * A.adjugate.transpose *
    Matrix.diagonal (ArithmeticQuotientEquationsData.diagonalCoefficient b)

lemma splitDualMatrix_map (b binv : R) (A : ArithmeticQuotientEquationsData.Mat R) (f : R →+* S) :
    (splitDualMatrix b binv A).map f = splitDualMatrix (f b) (f binv) (A.map f) := by
  have hd (x : R) : (Matrix.diagonal (ArithmeticQuotientEquationsData.diagonalCoefficient x)).map f =
      Matrix.diagonal (ArithmeticQuotientEquationsData.diagonalCoefficient (f x)) := by
    rw [Matrix.diagonal_map (map_zero f)]
    apply congrArg Matrix.diagonal
    funext i
    dsimp [ArithmeticQuotientEquationsData.diagonalCoefficient]
    split_ifs <;> simp
  have ha : A.adjugate.transpose.map f = (A.map f).adjugate.transpose :=
    congrArg Matrix.transpose (f.map_adjugate A)
  simp only [splitDualMatrix, Matrix.map_mul, hd, ha]

def splitDecodeMatrix (d b binv half invTwoRoot : R) (A : ArithmeticQuotientEquationsData.Mat R) :
    ArithmeticQuotientEquationsData.Mat (QuadraticAlgebra R d 0) := fun i j =>
  ⟨(A i j + splitDualMatrix b binv A i j) * half,
    (A i j - splitDualMatrix b binv A i j) * invTwoRoot⟩

lemma splitDecodeMatrix_map (d b binv half invTwoRoot : R) (A : ArithmeticQuotientEquationsData.Mat R) (f : R →+* S) :
    (splitDecodeMatrix d b binv half invTwoRoot A).map (ArithmeticQuotientEquationsData.quadraticMap d f) =
      splitDecodeMatrix (f d) (f b) (f binv) (f half) (f invTwoRoot) (A.map f) := by
  apply Matrix.ext
  intro i j
  have he := congrArg (fun M : ArithmeticQuotientEquationsData.Mat S => M i j) (splitDualMatrix_map b binv A f)
  change f (splitDualMatrix b binv A i j) =
    splitDualMatrix (f b) (f binv) (A.map f) i j at he
  apply QuadraticAlgebra.ext
  · change f ((A i j + splitDualMatrix b binv A i j) * half) = _
    simp only [splitDecodeMatrix, map_mul, map_add, he, Matrix.map_apply]
  · change f ((A i j - splitDualMatrix b binv A i j) * invTwoRoot) = _
    simp only [splitDecodeMatrix, map_mul, map_sub, he, Matrix.map_apply]

def splitLiftMatrix (d b binv half invTwoRoot : R) (A : ArithmeticQuotientEquationsData.Mat R) : Matrix (Fin 6) (Fin 6) R :=
  ArithmeticQuotientEquationsData.regularMatrix d (splitDecodeMatrix d b binv half invTwoRoot A)

lemma splitLiftMatrix_map (d b binv half invTwoRoot : R) (A : ArithmeticQuotientEquationsData.Mat R) (f : R →+* S) :
    (splitLiftMatrix d b binv half invTwoRoot A).map f =
      splitLiftMatrix (f d) (f b) (f binv) (f half) (f invTwoRoot) (A.map f) := by
  rw [splitLiftMatrix, ← ArithmeticQuotientEquationsData.regularMatrix_map, splitDecodeMatrix_map]
  rfl

end Ring

variable {K : Type} [Field K] [CharZero K]

def splitSLToPoints (d r b : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0) (hb : b ≠ 0) :
    ArithmeticQuotientEquationsData.SL K ≃* (unitaryAlgebraicGroup d b).RationalPoints :=
  (quadraticUnitaryEquivSL d r b hr hr0 hb).symm.trans (regularUnitaryEquiv d b)

lemma splitSLToPoints_matrix (d r b : K) (hr : r ^ 2 = d) (hr0 : r ≠ 0) (hb : b ≠ 0)
    (A : ArithmeticQuotientEquationsData.SL K) :
    (splitSLToPoints d r b hr hr0 hb A).val.val =
      splitLiftMatrix d b b⁻¹ (2⁻¹) ((2 * r)⁻¹) A.val := by
  change ArithmeticQuotientEquationsData.regularMatrix d ((quadraticUnitaryEquivSL d r b hr hr0 hb).symm A).val.val = _
  apply congrArg (ArithmeticQuotientEquationsData.regularMatrix d)
  apply Matrix.ext
  intro i j
  rw [quadraticUnitaryEquivSL_symm_entry]
  apply QuadraticAlgebra.ext <;>
    simp [splitQuadraticInverse, splitDecodeMatrix, splitDualMatrix, dualMatrix,
      formMatrix, div_eq_mul_inv]

end

end OAI.Geometry.ComplexBall.ArithmeticQuotientSplitUnitary

import OAI.RepresentationTheory.Weil.UnitarySplitting.DualPair

/-! # Trace Pairing -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.TracePairing.Construction

noncomputable section

section

/-! The trace tensor form is alternating and nondegenerate under the
actual Hermitian/skew-Hermitian and nondegeneracy hypotheses. -/

open scoped BigOperators Kronecker
open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem quadratic_automorphism_involutive [CharZero F] [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E) :
    Function.Involutive σ := by
  let : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hQuadratic }
  have hp : σ ^ 2 = 1 := by
    simpa only [IsGalois.card_aut_eq_finrank, hQuadratic] using
      (pow_card_eq_one' (x := σ))
  intro x
  have hx := congrArg (fun e : E ≃ₐ[F] E => e x) hp
  simpa only [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using hx

omit [DecidableEq I] in
theorem sesquilinear_add_left (σ : E ≃ₐ[F] E) (L : Matrix I I E)
    (x y z : I → E) :
    DualPair.Construction.sesquilinear σ L (x + y) z = DualPair.Construction.sesquilinear σ L x z + DualPair.Construction.sesquilinear σ L y z := by
  simp only [DualPair.Construction.sesquilinear, Pi.add_apply, map_add]
  exact add_dotProduct _ _ _

omit [DecidableEq I] in
theorem sesquilinear_add_right (σ : E ≃ₐ[F] E) (L : Matrix I I E)
    (x y z : I → E) :
    DualPair.Construction.sesquilinear σ L x (y + z) = DualPair.Construction.sesquilinear σ L x y + DualPair.Construction.sesquilinear σ L x z := by
  simp only [DualPair.Construction.sesquilinear, Matrix.mulVec_add, dotProduct_add]

omit [DecidableEq I] in
theorem sesquilinear_smul_left (σ : E ≃ₐ[F] E) (L : Matrix I I E)
    (a : F) (x y : I → E) :
    DualPair.Construction.sesquilinear σ L (a • x) y = a • DualPair.Construction.sesquilinear σ L x y := by
  unfold DualPair.Construction.sesquilinear
  have hc : (fun i => σ ((a • x) i)) = a • (fun i => σ (x i)) := by
    funext i
    exact σ.toLinearMap.map_smul a (x i)
  rw [hc, smul_dotProduct]

omit [DecidableEq I] in
theorem sesquilinear_smul_right (σ : E ≃ₐ[F] E) (L : Matrix I I E)
    (a : F) (x y : I → E) :
    DualPair.Construction.sesquilinear σ L x (a • y) = a • DualPair.Construction.sesquilinear σ L x y := by
  simp only [DualPair.Construction.sesquilinear, Matrix.mulVec_smul, dotProduct_smul]

/-- Bundled F-bilinearity of the explicit trace tensor pairing. -/
def traceTensorBilinear (σ : E ≃ₐ[F] E) (H : Matrix I I E) (K : Matrix J J E) :
    LinearMap.BilinForm F (I × J → E) where
  toFun x :=
    { toFun := DualPair.Construction.traceTensorPairing σ H K x
      map_add' := by
        intro y z
        simp only [DualPair.Construction.traceTensorPairing, sesquilinear_add_right, map_add, add_div]
      map_smul' := by
        intro a y
        simp only [DualPair.Construction.traceTensorPairing, sesquilinear_smul_right, map_smul,
          smul_eq_mul, mul_div_assoc, RingHom.id_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change DualPair.Construction.traceTensorPairing σ H K (x + y) z =
      DualPair.Construction.traceTensorPairing σ H K x z + DualPair.Construction.traceTensorPairing σ H K y z
    simp only [DualPair.Construction.traceTensorPairing, sesquilinear_add_left,
      map_add, add_div]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    change DualPair.Construction.traceTensorPairing σ H K (a • x) y = a • DualPair.Construction.traceTensorPairing σ H K x y
    simp only [DualPair.Construction.traceTensorPairing, sesquilinear_smul_left,
      map_smul, smul_eq_mul, mul_div_assoc]

omit [DecidableEq I] in
theorem conjugate_sesquilinear (σ : E ≃ₐ[F] E) (hσ : Function.Involutive σ)
    (L : Matrix I I E) (x y : I → E) :
    σ (DualPair.Construction.sesquilinear σ L y x) = DualPair.Construction.sesquilinear σ (DualPair.Construction.adjointMatrix σ L) x y := by
  simp only [DualPair.Construction.sesquilinear, Matrix.mulVec, dotProduct, Finset.mul_sum,
    map_sum, map_mul, DualPair.Construction.adjointMatrix, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hσ (y j)]
  ring

omit [DecidableEq I] in
theorem sesquilinear_neg (σ : E ≃ₐ[F] E) (L : Matrix I I E) (x y : I → E) :
    DualPair.Construction.sesquilinear σ (-L) x y = -DualPair.Construction.sesquilinear σ L x y := by
  simp only [DualPair.Construction.sesquilinear, Matrix.neg_mulVec, dotProduct_neg]

omit [DecidableEq I] [DecidableEq J] in
theorem traceTensorPairing_skew (σ : E ≃ₐ[F] E) (hσ : Function.Involutive σ)
    (H : Matrix I I E) (K : Matrix J J E)
    (hH : DualPair.Construction.adjointMatrix σ H = H) (hK : DualPair.Construction.adjointMatrix σ K = -K)
    (x y : I × J → E) :
    DualPair.Construction.traceTensorPairing σ H K y x = -DualPair.Construction.traceTensorPairing σ H K x y := by
  unfold DualPair.Construction.traceTensorPairing
  rw [← Algebra.trace_eq_of_algEquiv σ (DualPair.Construction.sesquilinear σ (H ⊗ₖ K) y x),
    conjugate_sesquilinear σ hσ, DualPair.Construction.adjointMatrix_kronecker, hH, hK]
  have hkron : H ⊗ₖ (-K) = -(H ⊗ₖ K) := by
    ext i j
    simp
  rw [hkron, sesquilinear_neg, map_neg, neg_div]

omit [DecidableEq I] [DecidableEq J] in
theorem traceTensorPairing_alternating [CharZero F]
    (σ : E ≃ₐ[F] E) (hσ : Function.Involutive σ)
    (H : Matrix I I E) (K : Matrix J J E)
    (hH : DualPair.Construction.adjointMatrix σ H = H) (hK : DualPair.Construction.adjointMatrix σ K = -K)
    (x : I × J → E) : DualPair.Construction.traceTensorPairing σ H K x x = 0 := by
  have h := traceTensorPairing_skew σ hσ H K hH hK x x
  have htwo : (2 : F) * DualPair.Construction.traceTensorPairing σ H K x x = 0 := by
    calc
      _ = DualPair.Construction.traceTensorPairing σ H K x x + DualPair.Construction.traceTensorPairing σ H K x x := two_mul _
      _ = 0 := add_eq_zero_iff_eq_neg.mpr h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Nondegeneracy follows from invertibility of the tensor matrix and
nondegeneracy of the field trace pairing. -/
theorem traceTensorPairing_nondegenerate [CharZero F] [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (H : Matrix I I E) (K : Matrix J J E)
    (hH : H.det ≠ 0) (hK : K.det ≠ 0)
    (x : I × J → E) (hx : ∀ y, DualPair.Construction.traceTensorPairing σ H K x y = 0) : x = 0 := by
  have hdet : (H ⊗ₖ K).det ≠ 0 := by
    rw [Matrix.det_kronecker]
    exact mul_ne_zero (pow_ne_zero _ hH) (pow_ne_zero _ hK)
  have hsurj : Function.Surjective (H ⊗ₖ K).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  funext i
  apply σ.injective
  change σ (x i) = σ 0
  rw [map_zero]
  apply (traceForm_nondegenerate F E).1
  intro a
  obtain ⟨y, hy⟩ := hsurj (Pi.single i a)
  have hh := hx y
  unfold DualPair.Construction.traceTensorPairing DualPair.Construction.sesquilinear at hh
  rw [hy, dotProduct_single] at hh
  exact (div_eq_zero_iff.mp hh).resolve_right (by norm_num)

/-- The original matrix hypotheses produce a genuine nondegenerate
alternating F-bilinear form, with no additional involution assumption. -/
theorem traceTensorBilinear_is_symplectic [CharZero F] [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
    (H : Matrix I I E) (K : Matrix J J E)
    (hHermitian : ∀ i j, H j i = σ (H i j))
    (hSkewHermitian : ∀ i j, K j i = -σ (K i j))
    (hHNondegenerate : H.det ≠ 0) (hKNondegenerate : K.det ≠ 0) :
    (traceTensorBilinear σ H K).IsAlt ∧
      (traceTensorBilinear σ H K).Nondegenerate := by
  have hσ := quadratic_automorphism_involutive hQuadratic σ
  have hH : DualPair.Construction.adjointMatrix σ H = H := by
    ext i j
    change σ (H j i) = H i j
    rw [hHermitian, hσ]
  have hK : DualPair.Construction.adjointMatrix σ K = -K := by
    ext i j
    change σ (K j i) = -K i j
    rw [hSkewHermitian, map_neg, hσ]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact traceTensorPairing_alternating σ hσ H K hH hK x
  · intro x hx
    exact traceTensorPairing_nondegenerate σ H K hHNondegenerate hKNondegenerate x hx
  · intro x hx
    apply traceTensorPairing_nondegenerate σ H K hHNondegenerate hKNondegenerate x
    intro y
    rw [traceTensorPairing_skew σ hσ H K hH hK]
    change -(traceTensorBilinear σ H K y x) = 0
    rw [hx y, neg_zero]

end

/-! Algebraic identities for the unitary Cayley forms used in the splitting
calculation. All adjoints are the specified quadratic-field automorphism. -/

open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (σ : E ≃ₐ[F] E)

omit [Fintype I] [DecidableEq I] in
theorem adjointMatrix_add (A B : Matrix I I E) :
    DualPair.Construction.adjointMatrix σ (A + B) = DualPair.Construction.adjointMatrix σ A + DualPair.Construction.adjointMatrix σ B := by
  ext i j
  exact map_add σ _ _

omit [Fintype I] [DecidableEq I] in
theorem adjointMatrix_sub (A B : Matrix I I E) :
    DualPair.Construction.adjointMatrix σ (A - B) = DualPair.Construction.adjointMatrix σ A - DualPair.Construction.adjointMatrix σ B := by
  ext i j
  exact map_sub σ _ _

omit [Fintype I] [DecidableEq I] in
theorem adjointMatrix_neg (A : Matrix I I E) : DualPair.Construction.adjointMatrix σ (-A) = -DualPair.Construction.adjointMatrix σ A := by
  ext i j
  exact map_neg σ _

omit [Fintype I] [DecidableEq I] in
theorem adjointMatrix_involutive (hσ : Function.Involutive σ) :
    Function.Involutive (DualPair.Construction.adjointMatrix σ : Matrix I I E → Matrix I I E) := by
  intro A
  ext i j
  exact hσ (A i j)

theorem adjointMatrix_det (A : Matrix I I E) : (DualPair.Construction.adjointMatrix σ A).det = σ A.det := by
  rw [DualPair.Construction.adjointMatrix, Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom A).symm

theorem unitary_adjoint_mul (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q) :
    DualPair.Construction.adjointMatrix σ (g.val : Matrix I I E) * Q = Q * (↑g.val⁻¹ : Matrix I I E) := by
  have hh := congrArg (fun A : Matrix I I E => A * (↑g.val⁻¹ : Matrix I I E)) g.property
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hh

theorem unitary_det_relation (Q : Matrix I I E) (hQ : Q.det ≠ 0)
    (g : DualPair.Construction.unitaryGroup σ Q) : σ (g.val : Matrix I I E).det * (g.val : Matrix I I E).det = 1 := by
  have hh := congrArg Matrix.det g.property
  rw [Matrix.det_mul, Matrix.det_mul, adjointMatrix_det] at hh
  apply mul_right_cancel₀ hQ
  calc
    (σ (g.val : Matrix I I E).det * (g.val : Matrix I I E).det) * Q.det =
        σ (g.val : Matrix I I E).det * Q.det * (g.val : Matrix I I E).det := by ring
    _ = Q.det := hh
    _ = 1 * Q.det := (one_mul _).symm

def unitaryDifferenceForm (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q) : Matrix I I E :=
  Q * ((g.val : Matrix I I E) - 1)

theorem unitaryDifferenceForm_adjoint (Q : Matrix I I E)
    (hQ : DualPair.Construction.adjointMatrix σ Q = -Q) (g : DualPair.Construction.unitaryGroup σ Q) :
    DualPair.Construction.adjointMatrix σ (unitaryDifferenceForm σ Q g) =
      Q * (↑g.val⁻¹ : Matrix I I E) * ((g.val : Matrix I I E) - 1) := by
  rw [unitaryDifferenceForm, DualPair.Construction.adjointMatrix_mul, adjointMatrix_sub, DualPair.Construction.adjointMatrix_one, hQ]
  rw [sub_mul, mul_neg, one_mul, unitary_adjoint_mul]
  simp only [mul_sub, mul_assoc, Units.inv_mul, mul_one]
  abel

theorem unitaryDifferenceForm_ker (Q : Matrix I I E) (hQ : Q.det ≠ 0)
    (g : DualPair.Construction.unitaryGroup σ Q) :
    LinearMap.ker (unitaryDifferenceForm σ Q g).mulVecLin =
      LinearMap.ker ((g.val : Matrix I I E) - 1).mulVecLin := by
  ext x
  change (Q * ((g.val : Matrix I I E) - 1)) *ᵥ x = 0 ↔
    ((g.val : Matrix I I E) - 1) *ᵥ x = 0
  rw [← Matrix.mulVec_mulVec]
  simpa only [Matrix.mulVec_zero] using
    (Matrix.mulVec_injective_of_det_ne_zero hQ).eq_iff
      (a := ((g.val : Matrix I I E) - 1) *ᵥ x) (b := 0)

theorem unitaryDifferenceForm_adjoint_ker (Q : Matrix I I E) (hQ : Q.det ≠ 0)
    (hskew : DualPair.Construction.adjointMatrix σ Q = -Q) (g : DualPair.Construction.unitaryGroup σ Q) :
    LinearMap.ker (DualPair.Construction.adjointMatrix σ (unitaryDifferenceForm σ Q g)).mulVecLin =
      LinearMap.ker (unitaryDifferenceForm σ Q g).mulVecLin := by
  rw [unitaryDifferenceForm_adjoint σ Q hskew, unitaryDifferenceForm_ker σ Q hQ]
  have hdet : (Q * (↑g.val⁻¹ : Matrix I I E)).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hQ
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g.val⁻¹)).ne_zero
  ext x
  change (Q * (↑g.val⁻¹ : Matrix I I E) * ((g.val : Matrix I I E) - 1)) *ᵥ x = 0 ↔
    ((g.val : Matrix I I E) - 1) *ᵥ x = 0
  rw [← Matrix.mulVec_mulVec]
  simpa only [Matrix.mulVec_zero] using
    (Matrix.mulVec_injective_of_det_ne_zero hdet).eq_iff
      (a := ((g.val : Matrix I I E) - 1) *ᵥ x) (b := 0)

def adjointMatrixUnit (u : (Matrix I I E)ˣ) : (Matrix I I E)ˣ where
  val := DualPair.Construction.adjointMatrix σ (u : Matrix I I E)
  inv := DualPair.Construction.adjointMatrix σ (↑u⁻¹ : Matrix I I E)
  val_inv := by rw [← DualPair.Construction.adjointMatrix_mul, Units.inv_mul, DualPair.Construction.adjointMatrix_one]
  inv_val := by rw [← DualPair.Construction.adjointMatrix_mul, Units.mul_inv, DualPair.Construction.adjointMatrix_one]

theorem adjoint_congruence_iff (hσ : Function.Involutive σ)
    (u : (Matrix I I E)ˣ) (A : Matrix I I E) :
    DualPair.Construction.adjointMatrix σ (DualPair.Construction.adjointMatrix σ (u : Matrix I I E) * A * (u : Matrix I I E)) =
        DualPair.Construction.adjointMatrix σ (u : Matrix I I E) * A * (u : Matrix I I E) ↔
      DualPair.Construction.adjointMatrix σ A = A := by
  rw [DualPair.Construction.adjointMatrix_mul, DualPair.Construction.adjointMatrix_mul, adjointMatrix_involutive σ hσ]
  rw [← mul_assoc]
  change (adjointMatrixUnit σ u : Matrix I I E) * DualPair.Construction.adjointMatrix σ A * (u : Matrix I I E) =
    (adjointMatrixUnit σ u : Matrix I I E) * A * (u : Matrix I I E) ↔ _
  constructor
  · intro h
    exact (adjointMatrixUnit σ u).isUnit.mul_left_cancel (u.isUnit.mul_right_cancel h)
  · intro h
    rw [h]

theorem unitary_cayley_numerator (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q) :
    DualPair.Construction.adjointMatrix σ ((g.val : Matrix I I E) - 1) * Q * ((g.val : Matrix I I E) + 1) =
      DualPair.Construction.adjointMatrix σ (g.val : Matrix I I E) * Q - Q * (g.val : Matrix I I E) := by
  rw [adjointMatrix_sub, DualPair.Construction.adjointMatrix_one]
  calc
    _ = DualPair.Construction.adjointMatrix σ (g.val : Matrix I I E) * Q * (g.val : Matrix I I E) +
        DualPair.Construction.adjointMatrix σ (g.val : Matrix I I E) * Q - Q * (g.val : Matrix I I E) - Q := by
          noncomm_ring
    _ = _ := by rw [g.property]; abel

def unitaryCayleyForm (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q) : Matrix I I E :=
  Q * ((g.val : Matrix I I E) + 1) * ((g.val : Matrix I I E) - 1)⁻¹

theorem unitaryCayleyForm_hermitian (hσ : Function.Involutive σ)
    (Q : Matrix I I E) (hQ : DualPair.Construction.adjointMatrix σ Q = -Q) (g : DualPair.Construction.unitaryGroup σ Q)
    (hg : ((g.val : Matrix I I E) - 1).det ≠ 0) :
    DualPair.Construction.adjointMatrix σ (unitaryCayleyForm σ Q g) = unitaryCayleyForm σ Q g := by
  let u := ((g.val : Matrix I I E) - 1).nonsingInvUnit (isUnit_iff_ne_zero.mpr hg)
  apply (adjoint_congruence_iff σ hσ u _).mp
  have hs : DualPair.Construction.adjointMatrix σ (u : Matrix I I E) * unitaryCayleyForm σ Q g * (u : Matrix I I E) =
      DualPair.Construction.adjointMatrix σ (g.val : Matrix I I E) * Q - Q * (g.val : Matrix I I E) := by
    change DualPair.Construction.adjointMatrix σ ((g.val : Matrix I I E) - 1) *
      (Q * ((g.val : Matrix I I E) + 1) * ((g.val : Matrix I I E) - 1)⁻¹) *
        ((g.val : Matrix I I E) - 1) = _
    rw [mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), mul_one]
    rw [← mul_assoc, unitary_cayley_numerator]
  rw [hs, adjointMatrix_sub, DualPair.Construction.adjointMatrix_mul, DualPair.Construction.adjointMatrix_mul,
    adjointMatrix_involutive σ hσ, hQ]
  noncomm_ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.TracePairing.Construction

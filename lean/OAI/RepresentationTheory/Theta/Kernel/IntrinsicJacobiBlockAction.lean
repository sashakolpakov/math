import OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion

/-! # Intrinsic Jacobi Block Action -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicJacobiBlockAction.Intrinsic

/-! Pure matrix algebra adapted from JacobiBlockAction.
The actual position/momentum action induces the classical
inverse-transpose Jacobi change and its quadratic correction. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I R) (Z : Matrix I I R)

theorem jacobi_fractional_left_identity (hZ : Z.IsSymm) (hJ : IsUnit (g.denominator Z).det) :
    (g.denominator Z)ᵀ * g.fractional Z = (g.numerator Z)ᵀ := by
  have h := congrArg Matrix.transpose (g.fractional_mul_denominator Z hJ)
  simpa only [Matrix.transpose_mul, (g.fractional_symmetric Z hZ hJ).eq] using h

theorem jacobi_linear_factor (hZ : Z.IsSymm) (hJ : IsUnit (g.denominator Z).det) :
    g.A - g.fractional Z * g.C = (g.denominator Z)⁻¹ᵀ := by
  have hid : (g.denominator Z)ᵀ * (g.A - g.fractional Z * g.C) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, jacobi_fractional_left_identity g Z hZ hJ]
    calc
      (g.denominator Z)ᵀ * g.A - (g.numerator Z)ᵀ * g.C =
          Z * (g.Cᵀ * g.A - g.Aᵀ * g.C) + (g.Dᵀ * g.A - g.Bᵀ * g.C) := by
        simp only [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator,
          Matrix.transpose_add, Matrix.transpose_mul, hZ.eq]
        noncomm_ring
      _ = 1 := by rw [g.ac, sub_self, mul_zero, zero_add, g.da_bc]
  simpa only [Matrix.transpose_nonsing_inv] using (Matrix.inv_eq_right_inv hid).symm

theorem jacobi_constant_factor (hJ : IsUnit (g.denominator Z).det) :
    g.B - g.fractional Z * g.D = -(g.A - g.fractional Z * g.C) * Z := by
  have hb : g.B = g.fractional Z * g.denominator Z - g.A * Z := by
    apply (eq_sub_iff_add_eq).mpr
    rw [g.fractional_mul_denominator Z hJ, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator, add_comm]
  rw [hb]
  unfold AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator
  noncomm_ring

theorem jacobi_phase_action (hZ : Z.IsSymm) (hJ : IsUnit (g.denominator Z).det) (q p : I → R) :
    (g.B *ᵥ q + g.A *ᵥ p) - g.fractional Z *ᵥ (g.D *ᵥ q + g.C *ᵥ p) =
      (g.denominator Z)⁻¹ᵀ *ᵥ (p - Z *ᵥ q) := by
  calc
    _ = (g.B - g.fractional Z * g.D) *ᵥ q +
        (g.A - g.fractional Z * g.C) *ᵥ p := by
      simp only [Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    _ = (g.A - g.fractional Z * g.C) *ᵥ (p - Z *ᵥ q) := by
      rw [jacobi_constant_factor g Z hJ, Matrix.neg_mul, Matrix.neg_mulVec,
        Matrix.mulVec_sub, Matrix.mulVec_mulVec]
      abel
    _ = _ := by rw [jacobi_linear_factor g Z hZ hJ]

theorem jacobi_position_action (q p : I → R) :
    g.D *ᵥ q + g.C *ᵥ p = g.C *ᵥ (p - Z *ᵥ q) + g.denominator Z *ᵥ q := by
  simp only [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, Matrix.mulVec_sub, Matrix.add_mulVec,
    Matrix.mulVec_mulVec]
  abel

theorem jacobi_pairing_correction (hJ : IsUnit (g.denominator Z).det) (q p : I → R) :
    q ⬝ᵥ (p - Z *ᵥ q) -
        (g.D *ᵥ q + g.C *ᵥ p) ⬝ᵥ ((g.denominator Z)⁻¹ᵀ *ᵥ (p - Z *ᵥ q)) =
      -((p - Z *ᵥ q) ⬝ᵥ (((g.denominator Z)⁻¹ * g.C) *ᵥ (p - Z *ᵥ q))) := by
  rw [jacobi_position_action, add_dotProduct]
  have hj : (g.denominator Z *ᵥ q) ⬝ᵥ ((g.denominator Z)⁻¹ᵀ *ᵥ (p - Z *ᵥ q)) =
      q ⬝ᵥ (p - Z *ᵥ q) := by
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec, dotProduct_comm]
  have hc : (g.C *ᵥ (p - Z *ᵥ q)) ⬝ᵥ ((g.denominator Z)⁻¹ᵀ *ᵥ (p - Z *ᵥ q)) =
      (p - Z *ᵥ q) ⬝ᵥ (((g.denominator Z)⁻¹ * g.C) *ᵥ (p - Z *ᵥ q)) := by
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]
  rw [hj, hc]
  abel

end RepresentationTheory.Theta.Kernel.IntrinsicJacobiBlockAction.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates

/-! Position/momentum Jacobi coordinates for an arbitrary finite index
type, including the native place and Hodge coefficient index. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM
open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiBlockAction.Intrinsic

variable {I : Type*} [Fintype I] [DecidableEq I]

def phaseParameter (Z : Matrix I I ℂ) (q p : I → ℝ) : I → ℂ :=
  (fun i => (p i : ℂ)) - Z.mulVec (fun i => (q i : ℂ))

omit [DecidableEq I] in
theorem real_mulVec_im (Z : Matrix I I ℂ) (q : I → ℝ) (i : I) :
    (Z.mulVec (fun j => (q j : ℂ)) i).im = (Z.map Complex.im).mulVec q i := by
  simp [Matrix.mulVec,dotProduct,Complex.mul_im]

theorem phase_parameter_injective (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (q p r s : I → ℝ)
    (h : phaseParameter Z.matrix q p = phaseParameter Z.matrix r s) : q = r ∧ p = s := by
  have him : (Z.matrix.map Complex.im).mulVec q = (Z.matrix.map Complex.im).mulVec r := by
    funext i
    have hi := congrArg Complex.im (congrFun h i)
    change (p i : ℂ).im - (Z.matrix.mulVec (fun j => (q j : ℂ)) i).im =
      (s i : ℂ).im - (Z.matrix.mulVec (fun j => (r j : ℂ)) i).im at hi
    simpa only [Complex.ofReal_im,zero_sub,real_mulVec_im,neg_inj] using hi
  have hq := Matrix.mulVec_injective_of_isUnit Z.imaginary_posDef.isUnit him
  refine ⟨hq,?_⟩
  subst r
  funext i
  have hi := congrArg Complex.re (congrFun h i)
  change p i - (Z.matrix.mulVec (fun j => (q j : ℂ)) i).re =
    s i - (Z.matrix.mulVec (fun j => (q j : ℂ)) i).re at hi
  exact sub_left_inj.mp hi

omit [DecidableEq I] in
theorem real_mulVec_cast (M : Matrix I I ℝ) (q : I → ℝ) :
    (fun i => (M.mulVec q i : ℂ)) = (M.map Complex.ofRealHom).mulVec (fun i => (q i : ℂ)) := by
  funext i
  exact Complex.ofRealHom.map_mulVec M q i

theorem phase_parameter_transform (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (q p : I → ℝ) :
    phaseParameter (g.transformSiegel Z).matrix (g.D.mulVec q + g.C.mulVec p)
      (g.B.mulVec q + g.A.mulVec p) = g.jacobiChange Z (phaseParameter Z.matrix q p) := by
  have hc (M N : Matrix I I ℝ) :
      (fun i => ((M.mulVec q + N.mulVec p) i : ℂ)) =
        (M.map Complex.ofRealHom).mulVec (fun i => (q i : ℂ)) +
          (N.map Complex.ofRealHom).mulVec (fun i => (p i : ℂ)) := by
    simp only [Pi.add_apply,Complex.ofReal_add]
    exact congrArg₂ (fun x y : I → ℂ => x + y) (real_mulVec_cast M q) (real_mulVec_cast N p)
  unfold phaseParameter
  rw [hc,hc,AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.transformSiegel_matrix,AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply]
  exact Intrinsic.jacobi_phase_action g.complexify Z.matrix Z.symmetric (g.denominator_det_isUnit Z) _ _

end RepresentationTheory.Theta.Kernel.IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates

end

end OAI

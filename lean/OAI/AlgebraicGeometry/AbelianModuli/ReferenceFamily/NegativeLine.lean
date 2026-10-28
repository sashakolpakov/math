import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OrthogonalHermitianCoordinates
import OAI.Geometry.ComplexBall.PrescribedSignsB

/-! # Negative Line -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine

noncomputable section

section

/-! Every negative line for the prescribed diagonal form has a unique
affine ball coordinate. The last coordinate cannot vanish because the
first two diagonal entries are positive. -/

open OAI.Geometry.ComplexBall.PrescribedSignsB

theorem complex_self_product_nonneg (z : ℂ) : 0 ≤ (z * star z).re := by
  change 0 ≤ z.re * z.re - z.im * (-z.im)
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

theorem negativeDiagonal_last_ne_zero (β : ℂ) (x : Fin 3 → ℂ)
    (hx : (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x x).re < 0) :
    x 2 ≠ 0 := by
  intro hz
  rw [OrthogonalHermitianCoordinates.complexHermitianMatrixForm_diagonal, hz] at hx
  simp only [star_zero, mul_zero, add_zero, Complex.add_re] at hx
  exact (not_lt_of_ge (add_nonneg (complex_self_product_nonneg (x 0))
    (complex_self_product_nonneg (x 1)))) hx

def negativeLineCoordinate (x : Fin 3 → ℂ) : Geometry.ComplexBall.PrescribedSignsB.BallChart :=
  fun i => x i.castSucc / x 2

theorem negativeLineCoordinate_vector (x : Fin 3 → ℂ) (hx : x 2 ≠ 0) :
    Geometry.ComplexBall.PrescribedSignsB.lineVector (negativeLineCoordinate x) = (x 2)⁻¹ • x := by
  ext i
  fin_cases i <;> simp [Geometry.ComplexBall.PrescribedSignsB.lineVector, negativeLineCoordinate, div_eq_mul_inv, mul_comm, hx]

theorem lineVector_span_injective : Function.Injective (fun z : Geometry.ComplexBall.PrescribedSignsB.BallChart =>
    Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}) := by
  intro z w h
  have hm : Geometry.ComplexBall.PrescribedSignsB.lineVector z ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} :=
    (congrArg (fun S : Submodule ℂ Geometry.ComplexBall.PrescribedSignsB.Vec => Geometry.ComplexBall.PrescribedSignsB.lineVector z ∈ S) h).mp (Submodule.mem_span_singleton_self _)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have ha1 : a = 1 := by
    have h2 := congrFun ha 2
    simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector] using h2
  rw [ha1, one_smul] at ha
  ext i
  fin_cases i
  · exact (congrFun ha 0).symm
  · exact (congrFun ha 1).symm

theorem exists_unique_negativeLine_coordinate (β : ℂ) (P : Submodule ℂ (Fin 3 → ℂ))
    (hdim : Module.finrank ℂ P = 1)
    (hneg : ∀ x ∈ P, x ≠ 0 →
      (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x x).re < 0) :
    ∃! z : Geometry.ComplexBall.PrescribedSignsB.BallChart, P = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} ∧
      (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0 := by
  have hp : 0 < Module.finrank ℂ P := hdim ▸ Nat.zero_lt_one
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
  have hnv : v.val ≠ 0 := fun h => hv (Subtype.ext h)
  have hlast : v.val 2 ≠ 0 := negativeDiagonal_last_ne_zero β v.val (hneg v.val v.property hnv)
  let z := negativeLineCoordinate v.val
  have hz : Geometry.ComplexBall.PrescribedSignsB.lineVector z ∈ P := (negativeLineCoordinate_vector v.val hlast).symm ▸
    P.smul_mem (v.val 2)⁻¹ v.property
  have hspan : Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} = P :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hz))
      ((finrank_span_singleton (Geometry.ComplexBall.PrescribedSignsB.lineVector_ne_zero z)).trans hdim.symm)
  refine ⟨z, ⟨hspan.symm, hneg _ hz (Geometry.ComplexBall.PrescribedSignsB.lineVector_ne_zero z)⟩, ?_⟩
  intro w hw
  exact lineVector_span_injective (hw.1.symm.trans hspan.symm)

end

section

/-! The affine negative-line formula describes the actual image of
the one-dimensional subspace under a complex-linear isomorphism. -/

open OAI.Geometry.ComplexBall.PrescribedSignsB

theorem negativeLineCoordinate_span (x : Fin 3 → ℂ) (hx : x 2 ≠ 0) :
    Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (negativeLineCoordinate x)} = Submodule.span ℂ {x} := by
  rw [negativeLineCoordinate_vector x hx]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hx)) x

theorem map_lineVector_span (f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : f (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0) :
    (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}).map f =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (negativeLineCoordinate (f (Geometry.ComplexBall.PrescribedSignsB.lineVector z)))} := by
  rw [Submodule.map_span, Set.image_singleton]
  exact (negativeLineCoordinate_span (f (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) hz).symm

def normalizedLineMap (eA eB f : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) :
    (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) := eA.trans (f.trans eB.symm)

theorem normalized_line_submodule_transport
    (P Q : Submodule ℂ (Fin 3 → ℂ))
    (eA eB f : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hP : P.map eA.symm.toLinearMap = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hQ : Q.map eB.symm.toLinearMap = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w})
    (hz : normalizedLineMap eA eB f (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0)
    (hw : w = negativeLineCoordinate (normalizedLineMap eA eB f (Geometry.ComplexBall.PrescribedSignsB.lineVector z))) :
    P.map f.toLinearMap = Q := by
  apply Submodule.map_injective_of_injective eB.symm.injective
  rw [hQ]
  have hn : eB.symm.toLinearMap.comp f.toLinearMap =
      (normalizedLineMap eA eB f).toLinearMap.comp eA.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun y => eB.symm (f y)) (eA.apply_symm_apply x).symm
  rw [← Submodule.map_comp, hn, Submodule.map_comp, hP]
  exact (map_lineVector_span (normalizedLineMap eA eB f).toLinearMap z hz).trans
    (congrArg (fun t => Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector t}) hw.symm)

theorem diagonalIsometry_last_ne_zero (β : ℂ)
    (f : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (hf : ∀ x y, ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) (f x) (f y) =
      ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x y)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0) :
    f (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0 :=
  negativeDiagonal_last_ne_zero β (f (Geometry.ComplexBall.PrescribedSignsB.lineVector z))
    ((congrArg (fun t : ℂ => t.re < 0) (hf (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).mpr hz)

end

/-! Explicit affine projective coordinates preserve the negative domain
and compose as the original linear maps. -/

open OAI.Geometry.ComplexBall.PrescribedSignsB

theorem hermitian_smul_self_real
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) →ₗ⋆[ℂ] ℂ) (c : ℂ) (x : Fin 3 → ℂ) :
    (F (c • x) (c • x)).re = Complex.normSq c * (F x x).re := by
  have h : F (c • x) (c • x) = (c * star c) * F x x := by
    simp only [map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
    change star c * (c * F x x) = c * star c * F x x
    ring
  rw [h, Complex.star_def, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem negativeLineCoordinate_negative (β : ℂ) (x : Fin 3 → ℂ)
    (hx : (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x x).re < 0) :
    (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β])
      (Geometry.ComplexBall.PrescribedSignsB.lineVector (negativeLineCoordinate x)) (Geometry.ComplexBall.PrescribedSignsB.lineVector (negativeLineCoordinate x))).re < 0 := by
  have hl := negativeDiagonal_last_ne_zero β x hx
  rw [negativeLineCoordinate_vector x hl, hermitian_smul_self_real]
  exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr (inv_ne_zero hl)) hx

theorem negativeLineCoordinate_smul (c : ℂ) (hc : c ≠ 0) (x : Fin 3 → ℂ) :
    negativeLineCoordinate (c • x) = negativeLineCoordinate x := by
  funext i
  change (c * x i.castSucc) / (c * x 2) = x i.castSucc / x 2
  exact mul_div_mul_left _ _ hc

theorem negativeLineCoordinate_lineVector (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : negativeLineCoordinate (Geometry.ComplexBall.PrescribedSignsB.lineVector z) = z := by
  funext i
  fin_cases i <;> simp [negativeLineCoordinate, Geometry.ComplexBall.PrescribedSignsB.lineVector]

theorem negativeLineCoordinate_comp
    (f g : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hg : g (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0) :
    negativeLineCoordinate (f (Geometry.ComplexBall.PrescribedSignsB.lineVector (negativeLineCoordinate (g (Geometry.ComplexBall.PrescribedSignsB.lineVector z))))) =
      negativeLineCoordinate ((f * g) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) := by
  rw [negativeLineCoordinate_vector _ hg, f.map_smul, negativeLineCoordinate_smul _ (inv_ne_zero hg)]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine

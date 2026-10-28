import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjoint
import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-! # Symbol Differential -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions

noncomputable section

section

/-! Fixed-symbol coordinate representation of the actual exterior derivative.
The symbol uses mathlib's alternatization, so the normalization agrees with
the genuine de Rham differential. -/

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

/-- Exterior multiplication by a real covector, with the de Rham normalization. -/
def exteriorDifferentialSymbol (n : ℕ) (ξ : E →L[ℝ] ℝ) : DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).comp
    (ContinuousLinearMap.smulRightL ℝ E (DifferentialForms.Manifold.Basic.FormValue E n) ξ)

omit [LinearOrder ι] in
theorem derivative_basis_expansion (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) :
    L = ∑ i, (b.coord i).toContinuousLinearMap.smulRight (L (b i)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  change L v = ∑ i, b.repr v i • L (b i)
  simpa only [map_sum, map_smul] using (congrArg L (b.sum_repr v)).symm

omit [LinearOrder ι] in
/-- The actual exterior derivative has constant first-order symbols in a fixed real basis. -/
theorem extDeriv_symbol_expansion (b : Module.Basis ι ℝ E) (n : ℕ)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    extDeriv a x = ∑ i, exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap
      (fderiv ℝ a x (b i)) := by
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ (fderiv ℝ a x) = _
  conv_lhs => rw [derivative_basis_expansion b n (fderiv ℝ a x)]
  rw [map_sum]
  rfl

/-- Actual alternating covectors as their coefficients on a real exterior basis. -/
def exteriorCoordinateLinearEquiv (b : Module.Basis ι ℝ E) (n : ℕ) :
    DifferentialForms.Manifold.Basic.FormValue E n ≃ₗ[ℂ] (Set.powersetCard ι n → ℂ) :=
  (DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n).trans ((b.exteriorPower n).constr ℂ).symm

abbrev ExteriorCoordinates (ι : Type*) (n : ℕ) := EuclideanSpace ℂ (Set.powersetCard ι n)

/-- Fixed finite-dimensional Hilbert coordinates for the genuine alternating covectors. -/
def exteriorCoordinateEquiv (b : Module.Basis ι ℝ E) (n : ℕ) :
    DifferentialForms.Manifold.Basic.FormValue E n ≃L[ℂ] ExteriorCoordinates ι n := by
  let e := exteriorCoordinateLinearEquiv b n
  letI : FiniteDimensional ℂ (DifferentialForms.Manifold.Basic.FormValue E n) := e.symm.finiteDimensional
  exact e.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Set.powersetCard ι n => ℂ)).symm

theorem exteriorCoordinateEquiv_apply (b : Module.Basis ι ℝ E) (n : ℕ)
    (a : DifferentialForms.Manifold.Basic.FormValue E n) (s : Set.powersetCard ι n) :
    exteriorCoordinateEquiv b n a s = a (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
  change DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n a (b.exteriorPower n s) = _
  rw [exteriorPower.basis_apply]
  exact DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti E n a _

def coordinateExteriorSymbol (b : Module.Basis ι ℝ E) (n : ℕ) (i : ι) :
    ExteriorCoordinates ι n →L[ℝ] ExteriorCoordinates ι (n + 1) :=
  ((exteriorCoordinateEquiv b (n + 1)).toContinuousLinearMap.restrictScalars ℝ).comp
    ((exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap).comp
      ((exteriorCoordinateEquiv b n).symm.toContinuousLinearMap.restrictScalars ℝ))

/-- In fixed Hilbert coordinates, the actual exterior derivative is exactly the operator
whose formal adjoint was derived by integration by parts. -/
theorem exteriorDerivative_in_coordinates (b : Module.Basis ι ℝ E) (n : ℕ)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (ha : DifferentiableAt ℝ a x) :
    exteriorCoordinateEquiv b (n + 1) (extDeriv a x) =
      LocalAdjoint.Constructions.firstOrderCoordinateOperator b (coordinateExteriorSymbol b n)
        (fun y => exteriorCoordinateEquiv b n (a y)) x := by
  have hd : fderiv ℝ (fun y => exteriorCoordinateEquiv b n (a y)) x =
      ((exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).comp (fderiv ℝ a x) :=
    (((exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp
      x ha.hasFDerivAt).fderiv
  rw [extDeriv_symbol_expansion b n a x, map_sum]
  unfold LocalAdjoint.Constructions.firstOrderCoordinateOperator
  apply Finset.sum_congr rfl
  intro i _
  rw [hd]
  change exteriorCoordinateEquiv b (n + 1)
    (exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap (fderiv ℝ a x (b i))) =
    exteriorCoordinateEquiv b (n + 1)
    (exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap
      ((exteriorCoordinateEquiv b n).symm (exteriorCoordinateEquiv b n (fderiv ℝ a x (b i)))))
  rw [ContinuousLinearEquiv.symm_apply_apply]

end

section

/-! The exact principal-symbol complex of the genuine exterior derivative.
Its contracting homotopy is insertion of a vector dual to the nonzero symbol. -/

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def exteriorContraction (n : ℕ) (w : E) : DifferentialForms.Manifold.Basic.FormValue E (n + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
  (ContinuousLinearMap.apply ℝ (DifferentialForms.Manifold.Basic.FormValue E n) w).comp
    (ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap)

theorem exteriorContraction_apply (n : ℕ) (w : E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (v : Fin n → E) :
    exteriorContraction n w a v = a (Matrix.vecCons w v) := rfl

theorem exteriorDifferentialSymbol_apply (n : ℕ) (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E n)
    (v : Fin (n + 1) → E) :
    exteriorDifferentialSymbol n ξ a v =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (ξ (v i) • a (i.removeNth v)) := by
  change ContinuousAlternatingMap.alternatizeUncurryFin (ξ.smulRight a) v = _
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  rfl

theorem exteriorSymbol_squared (n : ℕ) (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    exteriorDifferentialSymbol (n + 1) ξ (exteriorDifferentialSymbol n ξ a) = 0 := by
  let f := ξ.smulRight (ξ.smulRight a)
  have hf (x y : E) : f x y = f y x := by
    change ξ x • (ξ y • a) = ξ y • (ξ x • a)
    exact smul_comm _ _ _
  have heq : ξ.smulRight (exteriorDifferentialSymbol n ξ a) =
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).comp f := by
    apply ContinuousLinearMap.ext
    intro u
    change ξ u • (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ (ξ.smulRight a)) =
      ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ (ξ u • ξ.smulRight a)
    rw [map_smul]
  change ContinuousAlternatingMap.alternatizeUncurryFin
    (ξ.smulRight (exteriorDifferentialSymbol n ξ a)) = 0
  rw [heq]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric hf

theorem exteriorSymbol_contraction_zero (ξ : E →L[ℝ] ℝ) (w : E) (a : DifferentialForms.Manifold.Basic.FormValue E 0) :
    exteriorContraction 0 w (exteriorDifferentialSymbol 0 ξ a) = ξ w • a := by
  ext v
  change exteriorDifferentialSymbol 0 ξ a (Matrix.vecCons w v) = ξ w • a v
  rw [exteriorDifferentialSymbol_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, Fin.removeNth_zero]
  rfl

/-- Exterior multiplication and insertion have the exact de Rham normalization. -/
theorem exteriorSymbol_contraction (n : ℕ) (ξ : E →L[ℝ] ℝ) (w : E)
    (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    exteriorContraction (n + 1) w (exteriorDifferentialSymbol (n + 1) ξ a) +
      exteriorDifferentialSymbol n ξ (exteriorContraction n w a) = ξ w • a := by
  ext v
  change exteriorDifferentialSymbol (n + 1) ξ a (Matrix.vecCons w v) +
    exteriorDifferentialSymbol n ξ (exteriorContraction n w a) v = ξ w • a v
  rw [exteriorDifferentialSymbol_apply, Fin.sum_univ_succ, exteriorDifferentialSymbol_apply]
  have hremove (i : Fin (n + 1)) :
      i.succ.removeNth (Matrix.vecCons w v) = Matrix.vecCons w (i.removeNth v) :=
    Fin.cons_comp_succ_succAbove w v i
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, Fin.removeNth_zero,
    Matrix.cons_val_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    hremove, exteriorContraction_apply, Finset.sum_neg_distrib]
  abel

/-- At every nonzero real covector, every symbol-closed positive-degree form is symbol-exact. -/
theorem exteriorSymbol_exact (n : ℕ) (ξ : E →L[ℝ] ℝ) (hξ : ξ ≠ 0)
    (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (ha : exteriorDifferentialSymbol (n + 1) ξ a = 0) :
    ∃ b : DifferentialForms.Manifold.Basic.FormValue E n, exteriorDifferentialSymbol n ξ b = a := by
  have hex : ∃ w : E, ξ w ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hξ
    ext w
    exact hn w
  obtain ⟨w, hw⟩ := hex
  let u : E := (ξ w)⁻¹ • w
  have hu : ξ u = 1 := by simp only [u, map_smul, smul_eq_mul, inv_mul_cancel₀ hw]
  refine ⟨exteriorContraction n u a, ?_⟩
  have h := exteriorSymbol_contraction n ξ u a
  rw [ha, map_zero, zero_add, hu, one_smul] at h
  exact h

theorem exteriorSymbol_zero_injective (ξ : E →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    Function.Injective (exteriorDifferentialSymbol 0 ξ) := by
  have hex : ∃ w : E, ξ w ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hξ
    ext w
    exact hn w
  obtain ⟨w, hw⟩ := hex
  intro a b hab
  have h := congrArg (exteriorContraction 0 w) hab
  rw [exteriorSymbol_contraction_zero, exteriorSymbol_contraction_zero] at h
  exact (smul_right_injective _ hw) h

end

/-! Exterior multiplication and insertion commute with the corresponding
pullbacks of their covector and vector arguments. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exteriorDifferentialSymbol_pullback (n : ℕ) (L : F →L[ℝ] E) (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    (exteriorDifferentialSymbol n ξ a).compContinuousLinearMap L =
      exteriorDifferentialSymbol n (ξ.comp L) (a.compContinuousLinearMap L) := by
  ext v
  change exteriorDifferentialSymbol n ξ a (fun i => L (v i)) = _
  rw [exteriorDifferentialSymbol_apply, exteriorDifferentialSymbol_apply]
  rfl

theorem exteriorContraction_pullback (n : ℕ) (L : F →L[ℝ] E) (w : F) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    (exteriorContraction n (L w) a).compContinuousLinearMap L =
      exteriorContraction n w (a.compContinuousLinearMap L) := by
  ext v
  change a (Matrix.vecCons (L w) (fun i => L (v i))) = a (fun i => L (Matrix.vecCons w v i))
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions

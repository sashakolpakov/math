import OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothJacobian
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothComplexPoint
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Complex.Basic

/-! # Jacobian Regularity -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity

noncomputable section

/-!
# Selected Jacobian minors and analytic regularity

The selected coordinates are given by the actual injective map in a
submersive presentation. We split all variables into those in its image and
its complement, preserving the ordering of the selected minor.
-/

open scoped Classical ContDiff _root_.Topology

open Filter

variable {ι σ : Type*}

/-- Variables outside the image of the chosen injection are free coordinates. -/
abbrev FreeCoordinates (s : σ → ι) := {i : ι // i ∉ Set.range s}

/-- Order the variables as free coordinates followed by the chosen coordinates.
The latter retain exactly the order of the selected Jacobian columns. -/
def selectedIndexEquiv (s : σ → ι) (hs : Function.Injective s) :
    FreeCoordinates s ⊕ σ ≃ ι :=
  ((Equiv.sumCongr (Equiv.refl _) (Equiv.ofInjective s hs)).trans
    (Equiv.sumComm _ _)).trans (Equiv.Set.sumCompl (Set.range s))

@[simp]
theorem selectedIndexEquiv_free (s : σ → ι) (hs : Function.Injective s)
    (i : FreeCoordinates s) : selectedIndexEquiv s hs (Sum.inl i) = i.val := by
  simp [selectedIndexEquiv, Equiv.Set.sumCompl]

@[simp]
theorem selectedIndexEquiv_selected (s : σ → ι) (hs : Function.Injective s)
    (j : σ) : selectedIndexEquiv s hs (Sum.inr j) = s j := by
  simp [selectedIndexEquiv, Equiv.Set.sumCompl]

@[simp]
theorem selectedIndexEquiv_symm_free (s : σ → ι) (hs : Function.Injective s)
    (i : FreeCoordinates s) : (selectedIndexEquiv s hs).symm i.val = Sum.inl i := by
  apply (selectedIndexEquiv s hs).injective
  simp

@[simp]
theorem selectedIndexEquiv_symm_selected (s : σ → ι) (hs : Function.Injective s)
    (j : σ) : (selectedIndexEquiv s hs).symm (s j) = Sum.inr j := by
  apply (selectedIndexEquiv s hs).injective
  simp

/-- Split a vector into its free coordinates and its selected coordinates. -/
def splitCoordinates (s : σ → ι) (x : ι → ℂ) :
    (FreeCoordinates s → ℂ) × (σ → ℂ) :=
  (fun i => x i.val, fun j => x (s j))

/-- Recombining the two coordinate blocks recovers every original coordinate. -/
theorem splitCoordinates_reconstruct (s : σ → ι) (hs : Function.Injective s)
    (x : ι → ℂ) :
    (Sum.elim (splitCoordinates s x).1 (splitCoordinates s x).2) ∘
      (selectedIndexEquiv s hs).symm = x := by
  have h : Sum.elim (splitCoordinates s x).1 (splitCoordinates s x).2 =
      x ∘ selectedIndexEquiv s hs := by
    funext j
    cases j with
    | inl i => simp [splitCoordinates]
    | inr j => simp [splitCoordinates]
  rw [h]
  funext i
  simp

/-- The selected/free coordinate decomposition is an actual linear equivalence. -/
def selectedCoordinateLinearEquiv (s : σ → ι) (hs : Function.Injective s) :
    (ι → ℂ) ≃ₗ[ℂ] (FreeCoordinates s → ℂ) × (σ → ℂ) where
  toFun := splitCoordinates s
  invFun z := Sum.elim z.1 z.2 ∘ (selectedIndexEquiv s hs).symm
  left_inv := splitCoordinates_reconstruct s hs
  right_inv z := by
    ext j <;> simp [splitCoordinates]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Rewrite the actual polynomial relations in the selected/free coordinates. -/
def selectedPolynomialFamily (s : σ → ι) (hs : Function.Injective s)
    (P : σ → MvPolynomial ι ℂ) : σ → MvPolynomial (FreeCoordinates s ⊕ σ) ℂ :=
  fun j => MvPolynomial.rename (selectedIndexEquiv s hs).symm (P j)

/-- The reindexed relations have exactly the original values. -/
theorem selectedPolynomialFamily_eval (s : σ → ι) (hs : Function.Injective s)
    (P : σ → MvPolynomial ι ℂ) (x : ι → ℂ) (j : σ) :
    MvPolynomial.eval (Sum.elim (splitCoordinates s x).1 (splitCoordinates s x).2)
      (selectedPolynomialFamily s hs P j) = MvPolynomial.eval x (P j) := by
  rw [selectedPolynomialFamily, MvPolynomial.eval_rename, splitCoordinates_reconstruct]

/-- Differentiation in a selected block coordinate gives precisely that
selected column of the original formal Jacobian, with no rank-only replacement. -/
theorem selectedPolynomialFamily_pderiv_eval (s : σ → ι) (hs : Function.Injective s)
    (P : σ → MvPolynomial ι ℂ) (x : ι → ℂ) (j k : σ) :
    MvPolynomial.eval (Sum.elim (splitCoordinates s x).1 (splitCoordinates s x).2)
      (MvPolynomial.pderiv (Sum.inr k) (selectedPolynomialFamily s hs P j)) =
      MvPolynomial.eval x (MvPolynomial.pderiv (s k) (P j)) := by
  rw [selectedPolynomialFamily, ← selectedIndexEquiv_symm_selected s hs k,
    MvPolynomial.pderiv_rename (selectedIndexEquiv s hs).symm.injective,
    MvPolynomial.eval_rename, splitCoordinates_reconstruct]

section FiniteCoordinates

variable [Fintype ι]

/-- In finite dimensions, the coordinate splitting and its inverse are continuous. -/
def selectedCoordinateEquiv (s : σ → ι) (hs : Function.Injective s) :
    (ι → ℂ) ≃L[ℂ] (FreeCoordinates s → ℂ) × (σ → ℂ) :=
  (selectedCoordinateLinearEquiv s hs).toContinuousLinearEquiv

@[simp]
theorem selectedCoordinateEquiv_apply (s : σ → ι) (hs : Function.Injective s)
    (x : ι → ℂ) : selectedCoordinateEquiv s hs x = splitCoordinates s x := rfl

end FiniteCoordinates

section Invertibility

variable [Fintype σ]

/-- An actual continuous linear map is invertible when its columns on the
standard basis form a matrix with nonzero determinant. -/
theorem isInvertible_of_matrix_columns (L : (σ → ℂ) →L[ℂ] (σ → ℂ))
    (M : Matrix σ σ ℂ)
    (hcolumns : ∀ i j, L (Pi.single j 1) i = M i j)
    (hdet : M.det ≠ 0) : L.IsInvertible := by
  have hM : LinearMap.toMatrix' L.toLinearMap = M := by
    ext i j
    simpa only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe] using hcolumns i j
  have hL : L.det ≠ 0 := by
    change LinearMap.det L.toLinearMap ≠ 0
    rw [← LinearMap.det_toMatrix', hM]
    exact hdet
  exact ⟨L.toContinuousLinearEquivOfDetNeZero hL, by simp⟩

end Invertibility

section PolynomialDifferential

variable [Fintype ι] [Fintype σ]

/-- The usual concatenation of free and selected coordinate vectors. -/
def sumCoordinateMap : ((ι → ℂ) × (σ → ℂ)) →L[ℂ] (ι ⊕ σ → ℂ) :=
  (LinearEquiv.sumArrowLequivProdArrow ι σ ℂ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem sumCoordinateMap_apply (z : (ι → ℂ) × (σ → ℂ)) :
    sumCoordinateMap z = Sum.elim z.1 z.2 := rfl

@[simp]
theorem sumCoordinateMap_selected_single (j : σ) :
    (sumCoordinateMap (ι := ι)) (0, Pi.single j (1 : ℂ)) = Pi.single (Sum.inr j) 1 := by
  ext k
  cases k <;> simp [Pi.single_apply]

/-- The analytic derivative in each selected coordinate is the corresponding
formal partial derivative of the actual polynomial map. -/
theorem fderiv_splitPolynomialMap_selected_single
    (P : σ → MvPolynomial (ι ⊕ σ) ℂ)
    (u : (ι → ℂ) × (σ → ℂ)) (j k : σ) :
    (fderiv ℂ (PolynomialImplicit.splitPolynomialMap P) u (0, Pi.single j 1)) k =
      MvPolynomial.eval (Sum.elim u.1 u.2) (MvPolynomial.pderiv (Sum.inr j) (P k)) := by
  have hd : DifferentiableAt ℂ (PolynomialImplicit.splitPolynomialMap P) u :=
    (PolynomialImplicit.contDiff_splitPolynomialMap P 1).differentiable_one u
  have hc : HasFDerivAt (fun z => PolynomialImplicit.splitPolynomialMap P z k)
      ((fderiv ℂ (fun x => MvPolynomial.eval x (P k)) (sumCoordinateMap u)).comp
        sumCoordinateMap) u :=
    (PolynomialDerivative.differentiable_polynomial_eval (P k) (sumCoordinateMap u)).hasFDerivAt.comp u
      sumCoordinateMap.hasFDerivAt
  have h := congrArg (fun L => L (0, Pi.single j 1)) (fderiv_apply hd k)
  rw [hc.fderiv] at h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h
  rw [sumCoordinateMap_selected_single, PolynomialDerivative.fderiv_polynomial_eval_single] at h
  simpa only [sumCoordinateMap_apply] using h.symm

end PolynomialDifferential

variable {S : Type*} [CommRing S] [Algebra ℂ S]
variable [Fintype ι] [Fintype σ] [DecidableEq ι]

/-- The defining equations of a presentation, in its actual selected/free
coordinate splitting. -/
def presentationSplitPolynomials (P : Algebra.PreSubmersivePresentation ℂ S ι σ) :
    σ → MvPolynomial (FreeCoordinates P.map ⊕ σ) ℂ :=
  selectedPolynomialFamily P.map P.map_inj P.relation

/-- A field-valued point of the presented algebra in selected/free coordinates. -/
def presentationSplitPoint (P : Algebra.PreSubmersivePresentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) : (FreeCoordinates P.map → ℂ) × (σ → ℂ) :=
  splitCoordinates P.map (fun i => x (P.val i))

omit [Fintype ι] [Fintype σ] [DecidableEq ι] in
/-- Every presented algebra point satisfies the actual reindexed equations. -/
theorem presentationSplitPoint_zero
    (P : Algebra.PreSubmersivePresentation ℂ S ι σ) (x : S →ₐ[ℂ] ℂ) :
    PolynomialImplicit.splitPolynomialMap (presentationSplitPolynomials P) (presentationSplitPoint P x) = 0 := by
  ext j
  change MvPolynomial.eval _ (selectedPolynomialFamily P.map P.map_inj P.relation j) = 0
  simp only [presentationSplitPoint]
  rw [selectedPolynomialFamily_eval]
  exact Foundations.Scheme.StandardSmoothJacobian.Algebraic.point_relation_zero P.toPresentation x j

/-- The partial analytic derivative is represented by precisely the selected
algebraic Jacobian minor at the algebra point. -/
theorem presentation_partialDerivative_columns
    (P : Algebra.PreSubmersivePresentation ℂ S ι σ) (x : S →ₐ[ℂ] ℂ) (i j : σ) :
    ((fderiv ℂ (PolynomialImplicit.splitPolynomialMap (presentationSplitPolynomials P))
      (presentationSplitPoint P x)).comp
      (ContinuousLinearMap.inr ℂ (FreeCoordinates P.map → ℂ) (σ → ℂ)))
        (Pi.single j 1) i = Foundations.Scheme.StandardSmoothJacobian.Algebraic.pointJacobianMinor P x i j := by
  change (fderiv ℂ (PolynomialImplicit.splitPolynomialMap (presentationSplitPolynomials P))
    (presentationSplitPoint P x) (0, Pi.single j 1)) i = _
  rw [fderiv_splitPolynomialMap_selected_single]
  change MvPolynomial.eval _
      (MvPolynomial.pderiv (Sum.inr j)
        (selectedPolynomialFamily P.map P.map_inj P.relation i)) = _
  simp only [presentationSplitPoint]
  rw [selectedPolynomialFamily_pderiv_eval]
  rfl

/-- Submersive presentation data proves the exact analytic regularity hypothesis
of the implicit function theorem; no analytic rank assumption is added. -/
theorem standardSmooth_partialDerivative_isInvertible
    (P : Algebra.SubmersivePresentation ℂ S ι σ) (x : S →ₐ[ℂ] ℂ) :
    ((fderiv ℂ (PolynomialImplicit.splitPolynomialMap
      (presentationSplitPolynomials P.toPreSubmersivePresentation))
      (presentationSplitPoint P.toPreSubmersivePresentation x)).comp
      (ContinuousLinearMap.inr ℂ (FreeCoordinates P.map → ℂ) (σ → ℂ))).IsInvertible := by
  apply isInvertible_of_matrix_columns _
    (Foundations.Scheme.StandardSmoothJacobian.Algebraic.pointJacobianMinor P.toPreSubmersivePresentation x)
  · exact presentation_partialDerivative_columns P.toPreSubmersivePresentation x
  · exact Foundations.Scheme.StandardSmoothJacobian.Algebraic.pointJacobianMinor_det_ne_zero P x

/-- At every field-valued point, the zero set of a standard-smooth presentation
is locally an actual complex analytic graph in its selected coordinates. -/
theorem exists_standardSmooth_zero_graph
    (P : Algebra.SubmersivePresentation ℂ S ι σ) (x : S →ₐ[ℂ] ℂ) :
    let Q := presentationSplitPolynomials P.toPreSubmersivePresentation
    let u := presentationSplitPoint P.toPreSubmersivePresentation x
    ∃ ψ : (FreeCoordinates P.map → ℂ) → (σ → ℂ),
      ψ u.1 = u.2 ∧
      ContDiffAt ℂ ω ψ u.1 ∧
      (∀ᶠ y in 𝓝 u.1, PolynomialImplicit.splitPolynomialMap Q (y, ψ y) = 0) ∧
      (∀ᶠ z in 𝓝 u, PolynomialImplicit.splitPolynomialMap Q z = 0 ↔ ψ z.1 = z.2) := by
  exact PolynomialImplicit.exists_polynomial_zero_graph
    (presentationSplitPolynomials P.toPreSubmersivePresentation)
    (presentationSplitPoint P.toPreSubmersivePresentation x)
    (presentationSplitPoint_zero P.toPreSubmersivePresentation x)
    (standardSmooth_partialDerivative_isInvertible P x)

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity

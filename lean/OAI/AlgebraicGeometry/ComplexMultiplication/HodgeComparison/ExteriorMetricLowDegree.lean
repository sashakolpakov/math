import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointConjugation

/-! # Exterior Metric Low Degree -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ExteriorMetricLowDegree.CM.Construction

noncomputable section

/-! In degrees zero and one the exterior-power metric reduces to the
ordinary scalar and covector metrics, with their exact normalization. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exteriorOneEquiv_inner (x y : ⋀[ℝ]^1 E) :
    inner ℝ (exteriorPower.oneEquiv ℝ E x) (exteriorPower.oneEquiv ℝ E y) = inner ℝ x y := by
  have h : (innerₗ E).compl₁₂ (exteriorPower.oneEquiv ℝ E).toLinearMap
      (exteriorPower.oneEquiv ℝ E).toLinearMap = innerₗ (⋀[ℝ]^1 E) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    change inner ℝ (exteriorPower.oneEquiv ℝ E (exteriorPower.ιMulti ℝ 1 v))
      (exteriorPower.oneEquiv ℝ E (exteriorPower.ιMulti ℝ 1 w)) =
      inner ℝ (exteriorPower.ιMulti ℝ 1 v) (exteriorPower.ιMulti ℝ 1 w)
    rw [exteriorPower.oneEquiv_ιMulti, exteriorPower.oneEquiv_ιMulti, exteriorPower.inner_ιMulti_ιMulti,
      Matrix.det_fin_one]
    rfl
  exact congrArg (fun B : (⋀[ℝ]^1 E) →ₗ[ℝ] (⋀[ℝ]^1 E) →ₗ[ℝ] ℝ => B x y) h

def exteriorOneIsometry : (⋀[ℝ]^1 E) ≃ₗᵢ[ℝ] E :=
  (exteriorPower.oneEquiv ℝ E).isometryOfInner exteriorOneEquiv_inner

theorem exteriorZeroEquiv_inner (x y : ⋀[ℝ]^0 E) :
    inner ℝ (exteriorPower.zeroEquiv ℝ E x) (exteriorPower.zeroEquiv ℝ E y) = inner ℝ x y := by
  have h : (innerₗ ℝ).compl₁₂ (exteriorPower.zeroEquiv ℝ E).toLinearMap
      (exteriorPower.zeroEquiv ℝ E).toLinearMap = innerₗ (⋀[ℝ]^0 E) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    change inner ℝ (exteriorPower.zeroEquiv ℝ E (exteriorPower.ιMulti ℝ 0 v))
      (exteriorPower.zeroEquiv ℝ E (exteriorPower.ιMulti ℝ 0 w)) =
      inner ℝ (exteriorPower.ιMulti ℝ 0 v) (exteriorPower.ιMulti ℝ 0 w)
    rw [exteriorPower.zeroEquiv_ιMulti, exteriorPower.zeroEquiv_ιMulti, exteriorPower.inner_ιMulti_ιMulti]
    simp
  exact congrArg (fun B : (⋀[ℝ]^0 E) →ₗ[ℝ] (⋀[ℝ]^0 E) →ₗ[ℝ] ℝ => B x y) h

def exteriorZeroIsometry : (⋀[ℝ]^0 E) ≃ₗᵢ[ℝ] ℝ :=
  (exteriorPower.zeroEquiv ℝ E).isometryOfInner exteriorZeroEquiv_inner

def oneFormCovector (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : E →ₗ[ℝ] ℂ :=
  ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).symm f).toLinearMap

theorem exteriorCovectorEquiv_one (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E 1 f = (oneFormCovector f).comp (exteriorPower.oneEquiv ℝ E).toLinearMap := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E 1 f (exteriorPower.ιMulti ℝ 1 v) =
    oneFormCovector f (exteriorPower.oneEquiv ℝ E (exteriorPower.ιMulti ℝ 1 v))
  rw [exteriorPower.oneEquiv_ιMulti, Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti]
  change f v = f (fun _ => v 0)
  congr 1
  exact funext (fun i => congrArg v (Subsingleton.elim i 0))

theorem formMetricPair_one (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 1 f g = Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner (oneFormCovector f) (oneFormCovector g) := by
  rw [Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair, exteriorCovectorEquiv_one, exteriorCovectorEquiv_one]
  exact Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner_pullback_isometry (exteriorOneIsometry (E := E)) _ _

def zeroFormCovector (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 0) : ℝ →ₗ[ℝ] ℂ :=
  (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (f 0)

theorem exteriorCovectorEquiv_zero (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 0) :
    Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E 0 f = (zeroFormCovector f).comp (exteriorPower.zeroEquiv ℝ E).toLinearMap := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E 0 f (exteriorPower.ιMulti ℝ 0 v) =
    zeroFormCovector f (exteriorPower.zeroEquiv ℝ E (exteriorPower.ιMulti ℝ 0 v))
  rw [exteriorPower.zeroEquiv_ιMulti, Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti]
  change f v = (1 : ℝ) • f 0
  rw [one_smul]
  exact congrArg f (Subsingleton.elim v 0)

theorem formMetricPair_zero (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 0) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 0 f g = star (f 0) * g 0 := by
  rw [Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair, exteriorCovectorEquiv_zero, exteriorCovectorEquiv_zero]
  have h := Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner_pullback_isometry (exteriorZeroIsometry (E := E))
    (zeroFormCovector f) (zeroFormCovector g)
  calc
    _ = Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner (zeroFormCovector f) (zeroFormCovector g) := h
    _ = _ := by
      rw [Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner_eq_basis (OrthonormalBasis.singleton Unit ℝ)]
      simp [Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorBasisPair, zeroFormCovector]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ExteriorMetricLowDegree.CM.Construction

import OAI.Analysis.DifferentialForms.Manifold.ComplexAction
import OAI.Analysis.DifferentialForms.Manifold.BidegreeInvariant

/-! # Covector Action -/

namespace OAI.Analysis.DifferentialForms.Manifold

section

/-! The equivalence between actual chartwise pure type and the inverse-character
action on real tangent covectors used in the official Hodge statement. -/

open scoped _root_.Manifold ContDiff

attribute [local instance] ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {p q : ℕ}

/-- In preferred tangent coordinates, the ordinary pure-covector condition is
exactly the character condition for the actual complex action on real tangents. -/
theorem CovectorAction.hasBidegree_preferredChart_iff_tangent (form : Algebra.RawManifoldForm E M (p + q)) (x : M) :
    Bidegree.HasBidegree E p q (form.inChart (chartAt E x) (chartAt E x x)) ↔
      ∀ (z : ℂˣ) (v : Fin (p + q) → TangentSpace 𝓘(ℝ, E) x),
        form x (fun i => ComplexAction.complexTangentSMul x (z : ℂ) (v i)) =
          Bidegree.bidegreeCharacter p q z * form x v := by
  let e := TangentCoordinates.preferredTangentEquiv (E := E) x
  have he : form.inChart (chartAt E x) (chartAt E x x) =
      (form x).compContinuousLinearMap e.symm.toContinuousLinearMap := by
    ext v
    exact form.inChart_at (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x) v
  rw [he]
  constructor
  · intro hform z v
    have h := hform z (fun i => e (v i))
    change form x (fun i => e.symm ((z : ℂ) • e (v i))) =
      Bidegree.bidegreeCharacter p q z * form x (fun i => e.symm (e (v i))) at h
    change form x (fun i => e.symm ((z : ℂ) • e (v i))) =
      Bidegree.bidegreeCharacter p q z * form x v
    simpa only [e.symm_apply_apply] using h
  · intro hform z v
    have h := hform z (fun i => e.symm (v i))
    change form x (fun i => e.symm ((z : ℂ) • e (e.symm (v i)))) =
      Bidegree.bidegreeCharacter p q z * form x (fun i => e.symm (v i)) at h
    change form x (fun i => e.symm ((z : ℂ) • v i)) =
      Bidegree.bidegreeCharacter p q z * form x (fun i => e.symm (v i))
    simpa only [e.apply_symm_apply] using h

/-- The chartwise condition is the direct character condition for the
constructed, chart-independent complex tangent action. -/
theorem CovectorAction.hasManifoldBidegree_iff_tangent_action (form : Algebra.RawManifoldForm E M (p + q)) :
    ManifoldBidegree.HasManifoldBidegree E M p q form ↔
      ∀ (x : M) (z : ℂˣ) (v : Fin (p + q) → TangentSpace 𝓘(ℝ, E) x),
        form x (fun i => ComplexAction.complexTangentSMul x (z : ℂ) (v i)) =
          Bidegree.bidegreeCharacter p q z * form x v := by
  rw [BidegreeInvariant.hasManifoldBidegree_iff_chartAt]
  exact forall_congr' (fun x => CovectorAction.hasBidegree_preferredChart_iff_tangent form x)

variable (E M) in
/-- The type `(p,q)` inverse character on actual tangent covectors: a complex
scalar acts on a covector by pulling its arguments back by the inverse scalar.
This is the negative-power convention in the official statement. -/
def CovectorAction.HasTangentBidegree (p q : ℕ) (form : Algebra.RawManifoldForm E M (p + q)) : Prop :=
  ∀ (x : M) (z : ℂˣ) (v : Fin (p + q) → TangentSpace 𝓘(ℝ, E) x),
    form x (fun i => ComplexAction.complexTangentSMul x (↑(z⁻¹) : ℂ) (v i)) =
      (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ q)⁻¹) * form x v

/-- Actual chartwise pure type is exactly the official inverse-character
condition on the constructed complex tangent action. -/
theorem CovectorAction.hasManifoldBidegree_iff_tangentBidegree (form : Algebra.RawManifoldForm E M (p + q)) :
    ManifoldBidegree.HasManifoldBidegree E M p q form ↔ CovectorAction.HasTangentBidegree E M p q form := by
  rw [CovectorAction.hasManifoldBidegree_iff_tangent_action]
  constructor
  · intro hform x z v
    simpa only [Bidegree.bidegreeCharacter_inv] using hform x z⁻¹ v
  · intro hform x z v
    have h := hform x z⁻¹ v
    simpa [Bidegree.bidegreeCharacter] using h

/-- The inverse powers used above are literally the negative integer powers. -/
theorem CovectorAction.tangentBidegree_negative_powers (p q : ℕ) (z : ℂˣ) :
    (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ q)⁻¹) =
      (z : ℂ) ^ (-(p : ℤ)) * (star (z : ℂ)) ^ (-(q : ℤ)) := by
  simp

theorem ManifoldBidegree.PureManifoldForm.hasTangentBidegree (form : ManifoldBidegree.PureManifoldForm E M p q) :
    CovectorAction.HasTangentBidegree E M p q (form : Algebra.RawManifoldForm E M (p + q)) :=
  (CovectorAction.hasManifoldBidegree_iff_tangentBidegree (form : Algebra.RawManifoldForm E M (p + q))).mp
    form.hasManifoldBidegree

end

noncomputable section

/-! The actual inverse-scalar action on manifold covector sections and smooth forms. -/

open scoped _root_.Manifold ContDiff

attribute [local instance] ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n : ℕ}

/-- Complex multiplication also commutes with the actual inverse chart differential. -/
theorem CovectorAction.complexTangentSMul_chartInverse (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) (z : ℂ) (v : E) :
    ComplexAction.complexTangentSMul (e.symm y) z (Charts.chartInverseTangentMap e y v) =
      Charts.chartInverseTangentMap e y (z • v) := by
  apply (TangentCoordinates.chartTangentEquiv e he (e.symm y) (e.map_target hy)).injective
  change Charts.chartTangentMap e (e.symm y)
      (ComplexAction.complexTangentSMul (e.symm y) z (Charts.chartInverseTangentMap e y v)) =
    Charts.chartTangentMap e (e.symm y) (Charts.chartInverseTangentMap e y (z • v))
  have hcoord (w : E) : Charts.chartTangentMap e (e.symm y) (Charts.chartInverseTangentMap e y w) = w :=
    congrArg (fun f => f w) (Charts.chartTangentMap_comp_inverse e he hy)
  rw [ComplexAction.complexTangentSMul_inChart e he (e.symm y) (e.map_target hy), hcoord v, hcoord (z • v)]

section

/-- A scalar acts on a covector by pulling its tangent arguments back by the inverse scalar. -/
def Algebra.RawManifoldForm.complexAction (z : ℂˣ) : Algebra.RawManifoldForm E M n →ₗ[ℂ] Algebra.RawManifoldForm E M n where
  toFun form x := (form x).compContinuousLinearMap (ComplexAction.complexTangentScalarMap x (↑(z⁻¹) : ℂ))
  map_add' form other := by funext x; ext v; rfl
  map_smul' c form := by funext x; ext v; rfl

@[simp]
theorem Algebra.RawManifoldForm.complexAction_apply (z : ℂˣ) (form : Algebra.RawManifoldForm E M n) (x : M)
    (v : Fin n → TangentSpace 𝓘(ℝ, E) x) :
    Algebra.RawManifoldForm.complexAction z form x v =
      form x (fun i => ComplexAction.complexTangentSMul x (↑(z⁻¹) : ℂ) (v i)) := rfl

@[simp]
theorem Algebra.RawManifoldForm.complexAction_one (form : Algebra.RawManifoldForm E M n) : Algebra.RawManifoldForm.complexAction 1 form = form := by
  funext x
  ext v
  let := ComplexAction.complexTangentModule (E := E) x
  change form x (fun i => (↑((1 : ℂˣ)⁻¹) : ℂ) • v i) = form x v
  simp

theorem Algebra.RawManifoldForm.complexAction_mul (z w : ℂˣ) (form : Algebra.RawManifoldForm E M n) :
    Algebra.RawManifoldForm.complexAction (z * w) form = Algebra.RawManifoldForm.complexAction z (Algebra.RawManifoldForm.complexAction w form) := by
  funext x
  ext v
  let := ComplexAction.complexTangentModule (E := E) x
  change form x (fun i => (↑((z * w)⁻¹) : ℂ) • v i) =
    form x (fun i => (↑(w⁻¹) : ℂ) • ((↑(z⁻¹) : ℂ) • v i))
  simp only [mul_inv_rev, Units.val_mul, mul_smul]

/-- The section action becomes the usual scalar pullback on every chart expression. -/
theorem Algebra.RawManifoldForm.complexAction_inChart (z : ℂˣ) (form : Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    (Algebra.RawManifoldForm.complexAction z form).inChart e y =
      (form.inChart e y).compContinuousLinearMap
        (ContinuousLinearMap.lsmul ℝ ℂ (↑(z⁻¹) : ℂ)) := by
  ext v
  change form (e.symm y) (fun i =>
      ComplexAction.complexTangentSMul (e.symm y) (↑(z⁻¹) : ℂ) (Charts.chartInverseTangentMap e y (v i))) =
    form (e.symm y) (fun i => Charts.chartInverseTangentMap e y ((↑(z⁻¹) : ℂ) • v i))
  congr 1
  funext i
  exact CovectorAction.complexTangentSMul_chartInverse e he hy (↑(z⁻¹) : ℂ) (v i)

end

/-- The actual inverse-scalar section action preserves chartwise smoothness. -/
theorem Algebra.IsSmoothManifoldFormOn.complexAction {form : Algebra.RawManifoldForm E M n}
    {U : Set M} (hform : Algebra.IsSmoothManifoldFormOn form U) (z : ℂˣ) :
    Algebra.IsSmoothManifoldFormOn (Algebra.RawManifoldForm.complexAction z form) U := by
  intro e he
  let L : E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ (↑(z⁻¹) : ℂ)
  have hs :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (F := ℂ) (ι := Fin n) L).contDiff.comp_contDiffOn
      (hform e he)
  apply hs.congr
  intro y hy
  exact Algebra.RawManifoldForm.complexAction_inChart z form e he hy.1

section

/-- The inverse-scalar action as an actual complex-linear map on smooth forms. -/
def Algebra.SmoothManifoldForm.complexAction (z : ℂˣ) : Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Algebra.SmoothManifoldForm E M n where
  toFun form := ⟨Algebra.RawManifoldForm.complexAction z form.1, form.smooth.complexAction z⟩
  map_add' form other := Subtype.ext ((Algebra.RawManifoldForm.complexAction z).map_add form.1 other.1)
  map_smul' c form := Subtype.ext ((Algebra.RawManifoldForm.complexAction z).map_smul c form.1)

@[simp]
theorem Algebra.SmoothManifoldForm.complexAction_coe (z : ℂˣ) (form : Algebra.SmoothManifoldForm E M n) :
    (Algebra.SmoothManifoldForm.complexAction z form : Algebra.RawManifoldForm E M n) =
      Algebra.RawManifoldForm.complexAction z (form : Algebra.RawManifoldForm E M n) := rfl

@[simp]
theorem Algebra.SmoothManifoldForm.complexAction_one (form : Algebra.SmoothManifoldForm E M n) : Algebra.SmoothManifoldForm.complexAction 1 form = form := by
  apply Subtype.ext
  exact Algebra.RawManifoldForm.complexAction_one form.1

theorem Algebra.SmoothManifoldForm.complexAction_mul (z w : ℂˣ) (form : Algebra.SmoothManifoldForm E M n) :
    Algebra.SmoothManifoldForm.complexAction (z * w) form = Algebra.SmoothManifoldForm.complexAction z (Algebra.SmoothManifoldForm.complexAction w form) := by
  apply Subtype.ext
  exact Algebra.RawManifoldForm.complexAction_mul z w form.1

/-- The inverse-scalar maps give a group representation on genuine smooth forms. -/
def Algebra.SmoothManifoldForm.complexActionRepresentation : ℂˣ →* Module.End ℂ (Algebra.SmoothManifoldForm E M n) where
  toFun := Algebra.SmoothManifoldForm.complexAction
  map_one' := LinearMap.ext Algebra.SmoothManifoldForm.complexAction_one
  map_mul' z w := LinearMap.ext (Algebra.SmoothManifoldForm.complexAction_mul z w)

end

/-- The tangent eigencharacter condition is exactly an equality of actual covector sections. -/
theorem CovectorAction.hasTangentBidegree_iff_section_action {p q : ℕ} (form : Algebra.RawManifoldForm E M (p + q)) :
    CovectorAction.HasTangentBidegree E M p q form ↔ ∀ z : ℂˣ,
      Algebra.RawManifoldForm.complexAction z form =
        (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ q)⁻¹) • form := by
  constructor
  · intro hform z
    funext x
    ext v
    exact hform x z v
  · intro hform x z v
    exact congrArg (fun f : Algebra.RawManifoldForm E M (p + q) => f x v) (hform z)

end

end OAI.Analysis.DifferentialForms.Manifold

import OAI.Analysis.DifferentialForms.Manifold.Holomorphic
import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.AlgebraicTopology.DeRham.Comparison.TopBidegree

/-! # Pure Pullback -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-! Holomorphic pullback of actual pure manifold forms, including top-degree vanishing. -/

open scoped _root_.Manifold ContDiff

attribute [local instance] ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  [IsManifold 𝓘(ℂ, E) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ N] [IsManifold 𝓘(ℂ, G) ∞ P]
  {p q : ℕ}

/-- The actual manifold tangent pullback preserves pure bidegree along a
complex-smooth map. Its real derivative is proved to be complex-linear in charts. -/
theorem ManifoldBidegree.HasManifoldBidegree.pullback {form : Algebra.RawManifoldForm F N (p + q)}
    (hform : ManifoldBidegree.HasManifoldBidegree F N p q form) (g : M → N)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) :
    ManifoldBidegree.HasManifoldBidegree E M p q (form.pullback (E := E) g) := by
  intro e he y hy
  let f := chartAt F (g (e.symm y))
  have hf : f ∈ atlas F N := chart_mem_atlas F (g (e.symm y))
  have hfy : g (e.symm y) ∈ f.source := mem_chart_source F (g (e.symm y))
  rw [form.pullback_inChart g e f he hf hy hfy
    ((Holomorphic.contMDiff_real_of_complex hg).mdifferentiableAt (by simp))]
  have hhol :=
    (Holomorphic.complexContDiffAt_manifoldMap_inChart g e f he hf hy hfy hg.contMDiffAt).differentiableAt
      (by simp)
  rw [hhol.fderiv_restrictScalars ℝ]
  exact AlgebraicTopology.DeRham.Comparison.BidegreeRestriction.hasBidegree_pullback (hform f hf (f (g (e.symm y))) (f.map_source hfy))
    (fderiv ℂ (f ∘ g ∘ e.symm) y)

theorem PurePullback.complexPullback_mem_pureManifoldForm (g : M → N)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) {form : Algebra.SmoothManifoldForm F N (p + q)}
    (hform : form ∈ ManifoldBidegree.pureManifoldFormSubmodule F N p q) :
    Algebra.SmoothManifoldForm.pullback g (Holomorphic.contMDiff_real_of_complex hg) form ∈
      ManifoldBidegree.pureManifoldFormSubmodule E M p q :=
  ManifoldBidegree.HasManifoldBidegree.pullback hform g hg

/-- The same preservation statement for the official inverse tangent-action character. -/
theorem CovectorAction.HasTangentBidegree.pullback {form : Algebra.RawManifoldForm F N (p + q)}
    (hform : CovectorAction.HasTangentBidegree F N p q form) (g : M → N)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) :
    CovectorAction.HasTangentBidegree E M p q (form.pullback (E := E) g) :=
  (CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp
    (ManifoldBidegree.HasManifoldBidegree.pullback ((CovectorAction.hasManifoldBidegree_iff_tangentBidegree form).mpr hform) g hg)

section

/-- Holomorphic pullback on the actual smooth pure-type submodules. -/
def ManifoldBidegree.PureManifoldForm.pullback (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g) :
    ManifoldBidegree.PureManifoldForm F N p q →ₗ[ℂ] ManifoldBidegree.PureManifoldForm E M p q where
  toFun form := ⟨Algebra.SmoothManifoldForm.pullback g (Holomorphic.contMDiff_real_of_complex hg) form.1,
    PurePullback.complexPullback_mem_pureManifoldForm g hg form.2⟩
  map_add' form other := Subtype.ext
    ((Algebra.SmoothManifoldForm.pullback g (Holomorphic.contMDiff_real_of_complex hg)).map_add form.1 other.1)
  map_smul' c form := Subtype.ext
    ((Algebra.SmoothManifoldForm.pullback g (Holomorphic.contMDiff_real_of_complex hg)).map_smul c form.1)

@[simp]
theorem ManifoldBidegree.PureManifoldForm.pullback_coe (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (form : ManifoldBidegree.PureManifoldForm F N p q) :
    (ManifoldBidegree.PureManifoldForm.pullback g hg form : Algebra.SmoothManifoldForm E M (p + q)) =
      Algebra.SmoothManifoldForm.pullback g (Holomorphic.contMDiff_real_of_complex hg) form.1 := rfl

@[simp]
theorem ManifoldBidegree.PureManifoldForm.pullback_id (form : ManifoldBidegree.PureManifoldForm E M p q) :
    ManifoldBidegree.PureManifoldForm.pullback (id : M → M) contMDiff_id form = form := by
  apply Subtype.ext
  exact Algebra.SmoothManifoldForm.pullback_id form.1

theorem ManifoldBidegree.PureManifoldForm.pullback_comp (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (h : N → P) (hh : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, G) ∞ h)
    (form : ManifoldBidegree.PureManifoldForm G P p q) :
    ManifoldBidegree.PureManifoldForm.pullback (h ∘ g) (hh.comp hg) form = ManifoldBidegree.PureManifoldForm.pullback g hg (ManifoldBidegree.PureManifoldForm.pullback h hh form) := by
  apply Subtype.ext
  exact Algebra.SmoothManifoldForm.pullback_comp g (Holomorphic.contMDiff_real_of_complex hg)
    h (Holomorphic.contMDiff_real_of_complex hh) form.1

end

/-- An actual pure covector field of top real degree and unequal complex
degrees is zero on a complex manifold. -/
theorem PurePullback.pureManifoldForm_eq_zero_of_offDiagonal_top [FiniteDimensional ℂ E]
    {form : Algebra.RawManifoldForm E M (p + q)} (hform : ManifoldBidegree.HasManifoldBidegree E M p q form)
    (hdim : p + q = 2 * Module.finrank ℂ E) (hpq : p ≠ q) : form = 0 := by
  funext x
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hzero : form.inChart e (e x) = 0 :=
    AlgebraicTopology.DeRham.Comparison.TopBidegree.topContinuousAlternating_eq_zero_of_offDiagonal _
      (hform e he (e x) (e.map_source hx)) hdim hpq
  rw [← form.inChart_comp_chartTangentMap e he hx, hzero]
  ext v
  rfl

/-- Restriction along a holomorphic map kills a pure off-diagonal form whose
degree is the real dimension of the source manifold. -/
theorem PurePullback.complexPullback_eq_zero_of_pure_offDiagonal_top [FiniteDimensional ℂ E]
    (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    {form : Algebra.SmoothManifoldForm F N (p + q)}
    (hform : form ∈ ManifoldBidegree.pureManifoldFormSubmodule F N p q)
    (hdim : p + q = 2 * Module.finrank ℂ E) (hpq : p ≠ q) :
    Algebra.SmoothManifoldForm.pullback g (Holomorphic.contMDiff_real_of_complex hg) form = 0 := by
  apply Subtype.ext
  exact PurePullback.pureManifoldForm_eq_zero_of_offDiagonal_top (ManifoldBidegree.HasManifoldBidegree.pullback hform g hg)
    hdim hpq

end

end OAI.Analysis.DifferentialForms.Manifold

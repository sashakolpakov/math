import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodRealTorus
import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import Mathlib.Analysis.Calculus.MeanValue
import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws
import OAI.Analysis.DifferentialForms.Manifold.NormedSpace
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham
import OAI.Analysis.DifferentialForms.Manifold.DegreeZero

/-! # Forms Eq -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.FormsEq.Constructions.Forms

noncomputable section

/-!
# RiemannProjectivity: invariant closed forms on the actual period torus

Constant covectors descend through the lattice quotient because all period
chart transitions are translations. The resulting forms live on the actual
tangent spaces of the quotient manifold. Their exterior derivatives and
Hodge bidegrees use the project's existing differential-form definitions.
-/

open scoped _root_.NumberField ContDiff _root_.Manifold _root_.Topology
open Filter

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) {n : ℕ}

/-- A constant covector transferred to each actual tangent fiber. -/
def invariantRaw (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n :=
  fun q => OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (Φ.periodChart q) (fun _ => a) q

/-- The construction is independent of the chosen period chart at a point. -/
theorem invariantRaw_eq_chart (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n)
    (i q : Φ.periodTorus) (hq : q ∈ (Φ.periodChart i).source) :
    invariantRaw Φ a q =
      OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (Φ.periodChart i) (fun _ => a) q := by
  change a.compContinuousLinearMap (OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (Φ.periodChart q) q) =
    a.compContinuousLinearMap (OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (Φ.periodChart i) q)
  rw [Φ.periodChart_tangentMap_eq q i q (Φ.mem_periodChart_source q) hq]

/-- The descended form has exactly the original constant coefficients. -/
theorem invariantRaw_inChart (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n)
    (i : Φ.periodTorus) (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (hz : z ∈ (Φ.periodChart i).target) :
    (invariantRaw Φ a).inChart (Φ.periodChart i) z = a := by
  calc
    _ = (OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (Φ.periodChart i) (fun _ => a)).inChart
        (Φ.periodChart i) z := by
      unfold OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
      rw [invariantRaw_eq_chart Φ a i _ ((Φ.periodChart i).map_target hz)]
    _ = a := OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_fromChart_apply
      (Φ.periodChart i) (Φ.periodChart_mem_atlas i) (fun _ => a) hz

theorem invariantRaw_smooth (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (invariantRaw Φ a) Set.univ := by
  intro e he
  obtain ⟨i, rfl⟩ := he
  apply (contDiff_const : ContDiff ℝ ∞ (fun _ : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E => a)).contDiffOn.congr
  intro z hz
  exact invariantRaw_inChart Φ a i z hz.1

/-- A genuine smooth differential form on the quotient manifold. -/
def invariantForm (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n :=
  ⟨invariantRaw Φ a, invariantRaw_smooth Φ a⟩

/-- Constant coefficients have zero exterior derivative in every period chart. -/
theorem invariantForm_closed (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (invariantForm Φ a) = 0 := by
  apply OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro q
  have heq : (invariantRaw Φ a).inChart (Φ.periodChart q)
      =ᶠ[𝓝 (Φ.periodChart q q)] (fun _ => a) := by
    filter_upwards [(Φ.periodChart q).open_target.mem_nhds
      ((Φ.periodChart q).map_source (Φ.mem_periodChart_source q))] with z hz
    exact invariantRaw_inChart Φ a q z hz
  change (extDeriv ((invariantRaw Φ a).inChart (Φ.periodChart q))
    (Φ.periodChart q q)).compContinuousLinearMap (OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (Φ.periodChart q) q) = 0
  rw [heq.extDeriv_eq]
  have ha0 : extDeriv (fun _ : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E => a) (Φ.periodChart q q) = 0 := by
    unfold extDeriv
    rw [(hasFDerivAt_const (𝕜 := ℝ) a (Φ.periodChart q q)).fderiv]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ℂ)
  rw [ha0]
  ext v
  rfl

/-- A pure covector remains pure on the actual manifold. -/
theorem invariantForm_hasBidegree {p q : ℕ}
    (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (p + q))
    (ha : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) p q a) :
    OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus p q (invariantRaw Φ a) := by
  intro e he z hz
  obtain ⟨i, rfl⟩ := he
  rw [invariantRaw_inChart Φ a i z hz]
  exact ha

/-- Nonzero invariant covectors give nonzero actual forms. -/
theorem invariantForm_injective : Function.Injective
    (invariantForm Φ : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n →
      OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n) := by
  intro a b hab
  have hraw : invariantRaw Φ a = invariantRaw Φ b := congrArg Subtype.val hab
  let q : Φ.periodTorus := 0
  have hz := (Φ.periodChart q).map_source (Φ.mem_periodChart_source q)
  have h := congrArg (fun f : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n =>
    f.inChart (Φ.periodChart q) (Φ.periodChart q q)) hraw
  simpa only [invariantRaw_inChart Φ a q _ hz, invariantRaw_inChart Φ b q _ hz] using h

/-- A lattice-periodic function cannot have a nonzero constant derivative.
The proof uses the mean-value theorem and the full real span of the lattice. -/
theorem covector_zero_of_periodic_primitive
    (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
    (hF : ∀ z, HasFDerivAt F l z)
    (hperiodic : ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) = F z) : l = 0 := by
  have hlinear : F = fun z => l z + F 0 := by
    refine eq_of_fderiv_eq (fun z => (hF z).differentiableAt)
      (l.differentiable.add_const (F 0)) ?_ 0 ?_
    · intro z
      rw [(hF z).fderiv, (l.hasFDerivAt.add_const (F 0)).fderiv]
    · simp
  have hlattice : ∀ t ∈ Φ.periodIntegerLattice, l t = 0 := by
    intro t ht
    have h := hperiodic 0 t ht
    rw [hlinear] at h
    simpa using h
  have hspan : Submodule.span ℝ (Φ.periodIntegerLattice : Set (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)) ≤
      LinearMap.ker l.toLinearMap := by
    apply Submodule.span_le.mpr
    exact hlattice
  rw [IsZLattice.span_top] at hspan
  ext z
  exact hspan (Submodule.mem_top : z ∈ (⊤ : Submodule ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)))

/-- The period projection is smooth for the underlying real manifolds. -/
theorem projection_real_smooth :
    ContMDiff 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ∞
      (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus) := by
  intro z
  apply contMDiffAt_iff_target.mpr
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt, ?_⟩
  have hs := Φ.periodSection_realContDiffAt
    (Φ.periodChart (QuotientAddGroup.mk z)) (Φ.periodChart_symm _) z
    (Φ.mem_periodChart_source _)
  convert! hs.contMDiffAt using 1

/-- In the canonical real tangent coordinates, the differential of the
period projection followed by a local inverse is the identity. -/
theorem projection_tangent_identity (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :
    (OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (Φ.periodChart (QuotientAddGroup.mk z)) (QuotientAddGroup.mk z)).comp
      ((mfderiv 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)
        (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus) z).comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) := by
  have hchart := mdifferentiableAt_atlas (I := 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E))
    (Φ.periodChart_mem_atlas (QuotientAddGroup.mk z)) (Φ.mem_periodChart_source _)
  have hp := (projection_real_smooth Φ).mdifferentiable (by simp) z
  have hchain := mfderiv_comp (I := 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E))
    (I' := 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)) (I'' := 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)) z hchart hp
  rw [mfderiv_eq_fderiv] at hchain
  have hlocal := (Φ.periodSection_hasFDerivAt
    (Φ.periodChart (QuotientAddGroup.mk z)) (Φ.periodChart_symm _) z
    (Φ.mem_periodChart_source _)).fderiv
  apply ContinuousLinearMap.ext
  intro u
  exact congrArg (fun L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E => L u)
    (hchain.symm.trans hlocal)

/-- Pulling an invariant form to the vector-space cover recovers its
original constant coefficients, using actual tangent pullback. -/
theorem invariantForm_pullback (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n) :
    (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback
      (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus)
      (projection_real_smooth Φ) (invariantForm Φ a)).toNormedSpace =
      OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth (fun _ => a) contDiff_const := by
  apply OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro z
  ext v
  change a (fun i =>
    OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (Φ.periodChart (QuotientAddGroup.mk z)) (QuotientAddGroup.mk z)
      (mfderiv 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)
        (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus) z
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (v i)))) = a v
  congr 1
  funext i
  exact congrArg (fun L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E => L (v i))
    (projection_tangent_identity Φ z)

/-- A smooth global primitive of an invariant one-form forces its
covector to vanish. The argument takes place in the actual de Rham complex. -/
theorem invariant_oneForm_exact_imp_zero
    (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ)
    (f : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0)
    (hf : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = invariantForm Φ
      (ContinuousAlternatingMap.ofSubsingleton ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ℂ (0 : Fin 1) l)) :
    l = 0 := by
  let q : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus := QuotientAddGroup.mk
  let g : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 0 :=
    (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback q (projection_real_smooth Φ) f).toNormedSpace
  let F : OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) := g.toSmoothFunction
  have hd : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d g = OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth
      (fun _ => ContinuousAlternatingMap.ofSubsingleton ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ℂ
        (0 : Fin 1) l) contDiff_const := by
    rw [← OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.toNormedSpace_d, OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback, hf]
    exact invariantForm_pullback Φ _
  have hF : ∀ z, HasFDerivAt (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ) l z := by
    intro z
    have hdz : fderiv ℝ (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ) z = l := by
      ext v
      have h := congrArg (fun form : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 1 => form z (fun _ => v)) hd
      rw [← OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.toZeroForm_toSmoothFunction g] at h
      simp only [OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth_apply] at h
      exact h
    exact hdz ▸ (F.smooth.differentiable (by simp) z).hasFDerivAt
  have hvalue (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) : F z = f (q z) 0 := by
    change f (q z) (fun i : Fin 0 => _) = f (q z) 0
    congr 1
    exact Subsingleton.elim _ _
  apply covector_zero_of_periodic_primitive Φ l F hF
  intro z t ht
  rw [hvalue, hvalue]
  apply congrArg (fun p : Φ.periodTorus => f p 0)
  change (QuotientAddGroup.mk (z + t) : Φ.periodTorus) = QuotientAddGroup.mk z
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff t).mpr ht, add_zero]

/-- Invariant one-forms as genuine cocycles in the manifold de Rham complex. -/
def invariantClosedOneForm : (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) →ₗ[ℂ]
    OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 where
  toFun l := ⟨invariantForm Φ
    (ContinuousAlternatingMap.ofSubsingleton ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ℂ (0 : Fin 1) l),
    invariantForm_closed Φ _⟩
  map_add' l m := by
    apply Subtype.ext
    apply OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro q
    ext v
    rfl
  map_smul' c l := by
    apply Subtype.ext
    apply OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro q
    ext v
    rfl

/-- The actual first de Rham class of an invariant real-linear covector. -/
def invariantH1 : (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) →ₗ[ℂ]
    OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 :=
  (OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1).comp
    (invariantClosedOneForm Φ)

/-- Distinct invariant one-forms give distinct actual de Rham classes. -/
theorem invariantH1_injective : Function.Injective (invariantH1 Φ) := by
  intro l m hlm
  have hzero : invariantH1 Φ (l - m) = 0 := by
    rw [map_sub, hlm, sub_self]
  change OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1
    (invariantClosedOneForm Φ (l - m)) = 0 at hzero
  obtain ⟨f, hf⟩ := (OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff
    (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 _).mp hzero
  exact sub_eq_zero.mp (invariant_oneForm_exact_imp_zero Φ (l - m) f hf)

/-- Complex-linear covectors give closed forms of exactly the holomorphic
bidegree used by the manuscript and the project's geometric Hodge condition. -/
theorem complex_covector_holomorphic (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℂ] ℂ) :
    OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 0
      (invariantRaw Φ (OAI.Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) l)) :=
  invariantForm_hasBidegree Φ _ (OAI.Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) l)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.FormsEq.Constructions.Forms

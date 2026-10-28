import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates
import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws
import OAI.Analysis.DifferentialForms.Manifold.NormedSpace
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # Quotient Constant Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientConstantForms.CM.Construction.ComplexLatticeQuotient

noncomputable section

/-! Constant covectors descend to actual closed forms on the discrete
quotient. Pullback to the vector-space cover recovers their coefficients. -/

open Filter
open scoped ContDiff _root_.Manifold _root_.Topology
open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient
open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Λ : AddSubgroup E) [DiscreteTopology Λ] {n : ℕ}

def constantQuotientRaw (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) n :=
  fun q => Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q) (fun _ => a) q

theorem constantQuotientRaw_eq_chart (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (i q : QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ)
    (hq : q ∈ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i).source) :
    constantQuotientRaw Λ a q = Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i) (fun _ => a) q := by
  change a.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q) q) =
    a.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i) q)
  rw [QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.quotientChart_tangentMap_eq Λ q i q (QuotientManifold.CM.Construction.ComplexLatticeQuotient.mem_quotientChart_source Λ q) hq]

theorem constantQuotientRaw_inChart (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (i : QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) (z : E)
    (hz : z ∈ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i).target) :
    (constantQuotientRaw Λ a).inChart (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i) z = a := by
  calc
    _ = (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i) (fun _ => a)).inChart
        (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i) z := by
      unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
      rw [constantQuotientRaw_eq_chart Λ a i _ ((QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i).map_target hz)]
    _ = a := Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_fromChart_apply (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i)
      (QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.quotientChart_mem_atlas Λ i) (fun _ => a) hz

theorem constantQuotientRaw_smooth (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (constantQuotientRaw Λ a) Set.univ := by
  intro e he
  obtain ⟨i, rfl⟩ := he
  apply (contDiff_const : ContDiff ℝ ∞ (fun _ : E => a)).contDiffOn.congr
  intro z hz
  exact constantQuotientRaw_inChart Λ a i z hz.1

def constantQuotientForm (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) n :=
  ⟨constantQuotientRaw Λ a, constantQuotientRaw_smooth Λ a⟩

theorem constantQuotientForm_closed (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (constantQuotientForm Λ a) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro q
  have heq : (constantQuotientRaw Λ a).inChart (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q)
      =ᶠ[𝓝 (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q q)] (fun _ => a) := by
    filter_upwards [(QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q).open_target.mem_nhds
      ((QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q).map_source (QuotientManifold.CM.Construction.ComplexLatticeQuotient.mem_quotientChart_source Λ q))] with z hz
    exact constantQuotientRaw_inChart Λ a q z hz
  change (extDeriv ((constantQuotientRaw Λ a).inChart (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q))
    (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q q)).compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q) q) = 0
  rw [heq.extDeriv_eq]
  have ha0 : extDeriv (fun _ : E => a) (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q q) = 0 := by
    unfold extDeriv
    rw [(hasFDerivAt_const (𝕜 := ℝ) a (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q q)).fderiv]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
  rw [ha0]
  ext v
  rfl

theorem projection_tangent_identity (z : E) :
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ (QuotientAddGroup.mk z)) (QuotientAddGroup.mk z)).comp
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (QuotientAddGroup.mk : E → QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) z).comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ E := by
  have hchart := mdifferentiableAt_atlas (I := 𝓘(ℝ, E))
    (QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.quotientChart_mem_atlas Λ (QuotientAddGroup.mk z)) (QuotientManifold.CM.Construction.ComplexLatticeQuotient.mem_quotientChart_source Λ _)
  have hp := (QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.projection_realContMDiff Λ).mdifferentiable (by simp) z
  have hchain := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) z hchart hp
  rw [mfderiv_eq_fderiv] at hchain
  have hlocal := (QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.quotientSection_hasFDerivAt Λ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ (QuotientAddGroup.mk z))
    (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart_symm Λ _) z (QuotientManifold.CM.Construction.ComplexLatticeQuotient.mem_quotientChart_source Λ _)).fderiv
  apply ContinuousLinearMap.ext
  intro u
  exact congrArg (fun L : E →L[ℝ] E => L u) (hchain.symm.trans hlocal)

theorem constantQuotientForm_pullback (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (QuotientAddGroup.mk : E → QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ)
      (QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.projection_realContMDiff Λ) (constantQuotientForm Λ a)).toNormedSpace =
        Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth (fun _ => a) contDiff_const := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro z
  ext v
  change a (fun i => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ (QuotientAddGroup.mk z)) (QuotientAddGroup.mk z)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (QuotientAddGroup.mk : E → QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) z
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (v i)))) = a v
  congr 1
  funext i
  exact congrArg (fun L : E →L[ℝ] E => L (v i)) (projection_tangent_identity Λ z)

def constantQuotientClosedOneForm : (E →L[ℝ] ℂ) →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) 1 where
  toFun l := ⟨constantQuotientForm Λ (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) l),
    constantQuotientForm_closed Λ _⟩
  map_add' l m := by
    apply Subtype.ext
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro q
    ext v
    rfl
  map_smul' c l := by
    apply Subtype.ext
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro q
    ext v
    rfl

def constantQuotientH1 : (E →L[ℝ] ℂ) →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) 1 :=
  (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) 1).comp (constantQuotientClosedOneForm Λ)

variable [NormedSpace ℂ E]

theorem constantQuotientForm_hasBidegree {p q : ℕ} (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q))
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q a) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) p q (constantQuotientRaw Λ a) := by
  intro e he z hz
  obtain ⟨i, rfl⟩ := he
  rw [constantQuotientRaw_inChart Λ a i z hz]
  exact ha

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientConstantForms.CM.Construction.ComplexLatticeQuotient

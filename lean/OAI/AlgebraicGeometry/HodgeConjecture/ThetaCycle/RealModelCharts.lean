import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PureTopCoefficient
import OAI.Topology.Euclidean.ComplexModelRealCoordinates

/-! # Real Model Charts -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelCharts.CM

noncomputable section

/-! ThetaCycle: change the model coordinates of the actual manifold by an
explicit continuous linear equivalence. This supplies real charts for
the native fundamental-class integration comparison. -/

open scoped Classical _root_.Manifold ContDiff
open Set

variable {𝕜 E F M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace M] [ChartedSpace E M]

@[instance_reducible]
def linearRechartedSpace (e : E ≃L[𝕜] F) : ChartedSpace F M where
  atlas := (fun c : OpenPartialHomeomorph M E => c.trans e.toHomeomorph.toOpenPartialHomeomorph) '' atlas E M
  chartAt x := (chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp only [mfld_simps]
  chart_mem_atlas x := ⟨chartAt E x, chart_mem_atlas E x, rfl⟩

theorem linear_recharted_atlas (e : E ≃L[𝕜] F) (c : OpenPartialHomeomorph M F) :
    let _ := linearRechartedSpace (M := M) e
    c ∈ atlas F M ↔ ∃ a ∈ atlas E M, a.trans e.toHomeomorph.toOpenPartialHomeomorph = c := Iff.rfl

theorem linear_recharted_chart_apply (e : E ≃L[𝕜] F) (x y : M) :
    let _ := linearRechartedSpace (M := M) e
    chartAt F x y = e (chartAt E x y) := rfl

theorem linear_recharted_chart_symm_apply (e : E ≃L[𝕜] F) (x : M) (y : F) :
    let _ := linearRechartedSpace (M := M) e
    (chartAt F x).symm y = (chartAt E x).symm (e.symm y) := rfl

theorem linear_recharted_manifold (e : E ≃L[𝕜] F) (r : ℕ∞ω) [IsManifold 𝓘(𝕜, E) r M] :
    let _ := linearRechartedSpace (M := M) e
    IsManifold 𝓘(𝕜, F) r M := by
  let _ := linearRechartedSpace (M := M) e
  apply isManifold_of_contDiffOn 𝓘(𝕜, F) r M
  intro a b ha hb
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  have ho : ContDiffOn 𝕜 r (a.symm.trans b) (a.symm.trans b).source := by
    have h := (StructureGroupoid.compatible (contDiffGroupoid r 𝓘(𝕜, E)) ha hb).1
    simpa only [contDiffPregroupoid, mfld_simps] using h
  have hi : ContDiffOn 𝕜 r (fun y => (a.symm.trans b) (e.symm y))
      (e.symm ⁻¹' (a.symm.trans b).source) :=
    ho.comp e.symm.contDiff.contDiffOn (fun _ h => h)
  have h := e.contDiff.comp_contDiffOn hi
  simpa only [mfld_simps, ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.toHomeomorph_symm, Function.comp_def, preimage_preimage] using! h

/-- The coordinate change is the identity on the actual underlying manifold. -/
def linearRechartDiffeomorph (e : E ≃L[𝕜] F) (r : ℕ∞ω) :
    let _ := linearRechartedSpace (M := M) e
    M ≃ₘ^r⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ M := by
  let _ := linearRechartedSpace (M := M) e
  refine { toEquiv := Equiv.refl M, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    apply e.contDiff.contDiffWithinAt.congr_of_mem
    · intro y hy
      simp only [mfld_simps] at hy
      simpa only [mfld_simps, linearRechartedSpace, Function.comp_def] using!
        congrArg e ((chartAt E x).right_inv hy.1)
    · simp only [mfld_simps]
  · intro x
    refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    apply e.symm.contDiff.contDiffWithinAt.congr_of_mem
    · intro y hy
      simp only [mfld_simps] at hy
      have ht := hy.1
      change y ∈ ((chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph).target at ht
      have he : e.symm y ∈ (chartAt E x).target := by
        simpa only [mfld_simps] using! ht
      change (chartAt E x) ((chartAt F x).symm y) = e.symm y
      rw [linear_recharted_chart_symm_apply]
      exact (chartAt E x).right_inv he
    · simp only [mfld_simps]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelCharts.CM

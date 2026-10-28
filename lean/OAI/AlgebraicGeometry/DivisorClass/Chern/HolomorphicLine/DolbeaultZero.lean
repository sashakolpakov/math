import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothZeroFormFunctions

/-! # Dolbeault Zero -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.DolbeaultZero

noncomputable section

/-! The actual degree-zero Dolbeault operator on the constructed holomorphic line bundle. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicLineSmoothForm_dbar_compatible (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M)
    (s : AntiForms.HolomorphicLineSmoothForm u U 0) :
    (fun i => Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (s.val i)) ∈ AntiForms.holomorphicLineSmoothFormSubmodule u U 1 := by
  intro i j x hx hi hj
  let W := U ⊓ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)
  have hWi : W ≤ U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i :=
    fun _ hy => ⟨hy.1, hy.2.1⟩
  have hWj : W ≤ U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j :=
    fun _ hy => ⟨hy.1, hy.2.2⟩
  let g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := ↥W) :=
    (Holomorphic.Sheaves.holomorphicFunctionSheaf E M).obj.map (homOfLE (show W ≤
      Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j from inf_le_right)).op
        (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val
  have hs : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWj (s.val j) =
      SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g)
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWi (s.val i)) := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro z
    rw [SmoothScalarForm.smoothScalarOpenFormMul_apply]
    exact s.property i j z.val z.property.1 z.property.2.1 z.property.2.2
  have hd := congrArg (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0) hs
  rw [SmoothZeroFormFunctions.smoothHolomorphicScalar_dbar_mul_form, ← Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict,
    ← Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict] at hd
  have hv := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E W 1 => a ⟨x, hx, hi, hj⟩) hd
  have hg : (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) ⟨x, hx, hi, hj⟩ =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ := rfl
  simpa only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply, hg] using hv

def holomorphicLineDolbeaultZero (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    AntiForms.HolomorphicLineSmoothForm u U 0 →ₗ[ℂ] AntiForms.HolomorphicLineSmoothForm u U 1 where
  toFun s := ⟨fun i => Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (s.val i), holomorphicLineSmoothForm_dbar_compatible u U s⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0).map_add (s.val i) (t.val i)
  map_smul' z s := by
    apply Subtype.ext
    funext i
    exact (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0).map_smul z (s.val i)

theorem holomorphicLineDolbeaultZero_restrict {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U V : Opens M}
    (h : V ≤ U) (s : AntiForms.HolomorphicLineSmoothForm u U 0) :
    AntiForms.holomorphicLineSmoothFormRestrict h (holomorphicLineDolbeaultZero u U s) =
      holomorphicLineDolbeaultZero u V (AntiForms.holomorphicLineSmoothFormRestrict h s) := by
  apply Subtype.ext
  funext i
  exact Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict _ (s.val i)

theorem holomorphicLineDolbeaultZero_of_holomorphic (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M)
    (s : HolomorphicSection.Data.HolomorphicLineSection u U) :
    holomorphicLineDolbeaultZero u U (AntiForms.holomorphicLineSectionSmoothZeroForm u U s) = 0 := by
  apply Subtype.ext
  funext i
  exact Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_d (s.val i)

theorem holomorphicLineDolbeaultZero_coordinate_type (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M)
    (s : AntiForms.HolomorphicLineSmoothForm u U 0) (i : M) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree 0 1 ((holomorphicLineDolbeaultZero u U s).val i) :=
  Open.ManifoldDolbeault.openManifoldDolbeaultD_hasBidegree rfl (fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _)

theorem holomorphicLineDolbeaultZero_coordinate_closed (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M)
    (s : AntiForms.HolomorphicLineSmoothForm u U 0) (i : M) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 ((holomorphicLineDolbeaultZero u U s).val i) = 0 :=
  Manifold.DolbeaultCharts.openManifoldDolbeaultD_squared rfl (fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _)

variable [FiniteDimensional ℂ E]

theorem holomorphicLineDolbeaultZero_kernel (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    LinearMap.ker (holomorphicLineDolbeaultZero u U) =
      LinearMap.range (AntiForms.holomorphicLineSectionSmoothZeroForm u U) := by
  ext a
  constructor
  · intro ha
    have hlocal (i : M) : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (a.val i) = 0 :=
      congrArg (fun b : AntiForms.HolomorphicLineSmoothForm u U 1 => b.val i) ha
    let s : HolomorphicSection.Data.HolomorphicLineSection u U :=
      ⟨fun i => Manifold.DolbeaultZeroKernel.holomorphicManifoldFunctionOfDbarZero (a.val i) (hlocal i), by
        intro i j x hx hi hj
        exact congrArg (fun b : TangentSpace 𝓘(ℝ, E) x [⋀^Fin 0]→L[ℝ] ℂ => b 0)
          (a.property i j x hx hi hj)⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    funext i
    exact Manifold.DolbeaultZeroKernel.holomorphicManifoldZeroForm_ofDbarZero (a.val i) (hlocal i)
  · rintro ⟨s, rfl⟩
    exact holomorphicLineDolbeaultZero_of_holomorphic u U s

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.DolbeaultZero

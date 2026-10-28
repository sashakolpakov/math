import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.HolomorphicProduct
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.DolbeaultZero

/-! # Dolbeault -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Dolbeault

noncomputable section

/-! The genuine Dolbeault differential in every degree on the actual holomorphic line bundle. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicLineAntiForm_dbar_compatible (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (q : ℕ)
    (a : AntiForms.HolomorphicLineAntiForm u U q) :
    (fun i => Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q (a.val.val i)) ∈ AntiForms.holomorphicLineSmoothFormSubmodule u U (q + 1) := by
  intro i j x hx hi hj
  let W := U ⊓ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)
  have hWi : W ≤ U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i := fun _ hy => ⟨hy.1, hy.2.1⟩
  have hWj : W ≤ U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j := fun _ hy => ⟨hy.1, hy.2.2⟩
  let g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := ↥W) :=
    (Holomorphic.Sheaves.holomorphicFunctionSheaf E M).obj.map (homOfLE (show W ≤
      Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j from inf_le_right)).op
        (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val
  have hs : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWj (a.val.val j) =
      SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g)
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWi (a.val.val i)) := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro z
    rw [SmoothScalarForm.smoothScalarOpenFormMul_apply]
    exact a.val.property i j z.val z.property.1 z.property.2.1 z.property.2.2
  have hd := congrArg (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q) hs
  rw [Manifold.HolomorphicProduct.openManifoldDolbeaultD_holomorphic_mul g _ (by omega)
      (Open.ManifoldBidegree.openManifoldHasBidegree_restrict hWi (a.property i)),
    ← Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict, ← Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict] at hd
  have hv := congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E W (q + 1) => b ⟨x, hx, hi, hj⟩) hd
  have hg : (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) ⟨x, hx, hi, hj⟩ =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ := rfl
  simpa only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply, hg] using hv

def holomorphicLineDolbeault (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (q : ℕ) :
    AntiForms.HolomorphicLineAntiForm u U q →ₗ[ℂ] AntiForms.HolomorphicLineAntiForm u U (q + 1) where
  toFun a := ⟨⟨fun i => Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q (a.val.val i), holomorphicLineAntiForm_dbar_compatible u U q a⟩,
    fun i => Open.ManifoldDolbeault.openManifoldDolbeaultD_hasBidegree (by omega) (a.property i)⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q).map_add (a.val.val i) (b.val.val i)
  map_smul' z a := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q).map_smul z (a.val.val i)

theorem holomorphicLineDolbeault_squared (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (q : ℕ)
    (a : AntiForms.HolomorphicLineAntiForm u U q) :
    holomorphicLineDolbeault u U (q + 1) (holomorphicLineDolbeault u U q a) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact Manifold.DolbeaultCharts.openManifoldDolbeaultD_squared (by omega) (a.property i)

theorem holomorphicLineDolbeault_restrict {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U V : Opens M}
    (q : ℕ) (h : V ≤ U) (a : AntiForms.HolomorphicLineAntiForm u U q) :
    AntiForms.holomorphicLineAntiFormRestrict h (holomorphicLineDolbeault u U q a) =
      holomorphicLineDolbeault u V q (AntiForms.holomorphicLineAntiFormRestrict h a) := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict _ (a.val.val i)

theorem holomorphicLineDolbeault_zero_coe (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M)
    (a : AntiForms.HolomorphicLineAntiForm u U 0) :
    (holomorphicLineDolbeault u U 0 a).val = DolbeaultZero.holomorphicLineDolbeaultZero u U a.val := rfl

def holomorphicLineDolbeaultInclusion (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    HolomorphicSection.Data.HolomorphicLineSection u U →ₗ[ℂ] AntiForms.HolomorphicLineAntiForm u U 0 :=
  (AntiForms.holomorphicLineAntiZeroEquiv u U).toLinearMap.comp (AntiForms.holomorphicLineSectionSmoothZeroForm u U)

theorem holomorphicLineDolbeaultInclusion_d (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M)
    (s : HolomorphicSection.Data.HolomorphicLineSection u U) :
    holomorphicLineDolbeault u U 0 (holomorphicLineDolbeaultInclusion u U s) = 0 := by
  apply Subtype.ext
  rw [holomorphicLineDolbeault_zero_coe]
  exact DolbeaultZero.holomorphicLineDolbeaultZero_of_holomorphic u U s

variable [FiniteDimensional ℂ E]

theorem holomorphicLineDolbeault_zero_kernel (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    LinearMap.ker (holomorphicLineDolbeault u U 0) = LinearMap.range (holomorphicLineDolbeaultInclusion u U) := by
  ext a
  constructor
  · intro ha
    have hzero : DolbeaultZero.holomorphicLineDolbeaultZero u U a.val = 0 := by
      rw [← holomorphicLineDolbeault_zero_coe]
      exact congrArg (fun b : AntiForms.HolomorphicLineAntiForm u U 1 => b.val) ha
    have hr : a.val ∈ LinearMap.range (AntiForms.holomorphicLineSectionSmoothZeroForm u U) := by
      rw [← DolbeaultZero.holomorphicLineDolbeaultZero_kernel]
      exact hzero
    obtain ⟨s, hs⟩ := hr
    exact ⟨s, Subtype.ext hs⟩
  · rintro ⟨s, rfl⟩
    exact holomorphicLineDolbeaultInclusion_d u U s

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Dolbeault

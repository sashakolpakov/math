import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Projective
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts

/-! # Scheme Differentiable -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.SchemeDifferentiable

noncomputable section

section

/-! The generating section family defines actual complex points of the original projective scheme, with exact native coordinate ratios. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) {n : ℕ}
  (s : Fin (n + 1) → Data.HolomorphicLineSection u ⊤)
  (hs : ∀ x : V.analyticSpace, ∃ j, Nonzero.holomorphicSectionNonzeroAt u (s j) x)

def holomorphicSectionSchemeMap : V.analyticSpace → (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticSpace :=
  ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n ∘ Projective.holomorphicSectionProjectiveMap u s hs

theorem holomorphicSectionSchemeMap_continuous : Continuous (holomorphicSectionSchemeMap V u s hs) :=
  (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).continuous.comp (Projective.holomorphicSectionProjectiveMap_continuous u s hs)

theorem holomorphicSectionSchemeMap_patch (j : Fin (n + 1)) (x : V.analyticSpace)
    (hx : Nonzero.holomorphicSectionNonzeroAt u (s j) x) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (holomorphicSectionSchemeMap V u s hs x)) := by
  simpa only [holomorphicSectionSchemeMap, Function.comp_def, Homeomorph.symm_apply_apply] using
    (Projective.holomorphicSectionProjectiveMap_inPatch u s hs j x).mpr hx

theorem holomorphicSectionSchemeMap_chart_source (j : Fin (n + 1)) (x : V.analyticSpace)
    (hx : Nonzero.holomorphicSectionNonzeroAt u (s j) x) :
    holomorphicSectionSchemeMap V u s hs x ∈ (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart n j).source :=
  ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart_mem_source n j _ (holomorphicSectionSchemeMap_patch V u s hs j x hx)

theorem holomorphicSectionSchemeMap_chart (j : Fin (n + 1)) (x : V.analyticSpace)
    (hx : Nonzero.holomorphicSectionNonzeroAt u (s j) x) :
    ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart n j (holomorphicSectionSchemeMap V u s hs x) =
      fun k => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j ((Fintype.equivFin {l : Fin (n + 1) // l ≠ j}).symm k).val
        (Projective.holomorphicSectionProjectiveMap u s hs x) := by
  funext k
  have heq := ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart_apply n j (holomorphicSectionSchemeMap V u s hs x)
    (holomorphicSectionSchemeMap_patch V u s hs j x hx) k
  simpa only [holomorphicSectionSchemeMap, Function.comp_def, Homeomorph.symm_apply_apply] using heq

end

/-! The actual scheme-valued generating map is holomorphic in the original native scheme manifold structures. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

local instance sectionProjectiveCharted (n : ℕ) :
    ChartedSpace (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) :=
  (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticSpace_chartedSpace

theorem holomorphicSectionSchemeMap_mdifferentiable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) {n : ℕ}
    (s : Fin (n + 1) → Data.HolomorphicLineSection u ⊤)
    (hs : ∀ x : V.analyticSpace, ∃ j, Nonzero.holomorphicSectionNonzeroAt u (s j) x) :
    MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel)
      (holomorphicSectionSchemeMap V u s hs) := by
  intro x
  obtain ⟨j, hj⟩ := hs x
  let e := ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart n j
  let g : V.analyticSpace → (Fin (Fintype.card {l : Fin (n + 1) // l ≠ j}) → ℂ) :=
    fun y k => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j ((Fintype.equivFin {l : Fin (n + 1) // l ≠ j}).symm k).val
      (Projective.holomorphicSectionProjectiveMap u s hs y)
  have hg : ContMDiffAt 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Fin (Fintype.card {l : Fin (n + 1) // l ≠ j}) → ℂ) ∞ g x := by
    apply contMDiffAt_pi_space.mpr
    intro k
    exact Projective.holomorphicSectionProjectiveMap_ratio_at u s hs j _ x hj
  have hxsource : holomorphicSectionSchemeMap V u s hs x ∈ e.source :=
    holomorphicSectionSchemeMap_chart_source V u s hs j x hj
  have hxchart : e (holomorphicSectionSchemeMap V u s hs x) = g x :=
    holomorphicSectionSchemeMap_chart V u s hs j x hj
  have htarget : g x ∈ e.target := hxchart ▸ e.map_source hxsource
  have hi := (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart_mdifferentiable n j).mdifferentiableAt_symm htarget
  have hcomp := hi.comp x (hg.mdifferentiableAt (by simp))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(Nonzero.holomorphicSectionNonzeroAt_isOpen u (s j)).mem_nhds hj] with y hy
  have hcy : e (holomorphicSectionSchemeMap V u s hs y) = g y :=
    holomorphicSectionSchemeMap_chart V u s hs j y hy
  change holomorphicSectionSchemeMap V u s hs y = e.symm (g y)
  rw [← hcy]
  exact (e.left_inv (holomorphicSectionSchemeMap_chart_source V u s hs j y hy)).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.SchemeDifferentiable

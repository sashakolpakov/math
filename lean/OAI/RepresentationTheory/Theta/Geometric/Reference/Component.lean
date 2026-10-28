import OAI.RepresentationTheory.Theta.Geometric.Projective.AnalyticConnected
import OAI.RepresentationTheory.Theta.Geometric.Reference.LocusClosed
import OAI.RepresentationTheory.Theta.Geometric.Reference.SurfaceComponent

/-! # Component -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Once an actual integral projective PEL component contains one reference
point, every one of its complex points is an original reference moduli point. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)

theorem Data.ActiveHeckeThetaData.referenceLocus_eq_univ (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ D.pel.complexSpace)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hne : (D.referenceLocus hg f).Nonempty) : D.referenceLocus hg f = Set.univ := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : ConnectedSpace X.analyticSpace := Projective.AnalyticConnected.projective_analytic_connected X
  exact (D.referenceLocus_isClopen hg f hs hdegree).eq_univ hne

theorem Data.ActiveHeckeThetaData.exists_full_reference_surface_component
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ j : Fin D.pel.componentCount, (D.componentVariety hg j).complexDimension = 2 ∧
      ∀ x : (D.componentVariety hg j).analyticSpace, ∃ a : D.domain,
        x ≫ D.componentComplexInclusion j = D.referenceModuliMap hg a := by
  obtain ⟨j, hj, a, x, hx⟩ := D.exists_reference_surface_component hg hs hdegree
  have h := D.referenceLocus_eq_univ hg (D.componentVariety hg j) (D.componentComplexInclusion j)
    hs hdegree ⟨x, a, hx⟩
  refine ⟨j, hj, ?_⟩
  intro y
  have hy : y ∈ D.referenceLocus hg (D.componentComplexInclusion j) := by rw [h]; trivial
  exact hy

end

end OAI.RepresentationTheory.Theta.Geometric

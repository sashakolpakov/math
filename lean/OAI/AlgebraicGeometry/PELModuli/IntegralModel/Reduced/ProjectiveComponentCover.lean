import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ReducedComplexPEL
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ClosedLift
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexPointOpenCover

/-! # Projective Component Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ProjectiveComponentCover

noncomputable section

/-! ReferenceFamily's actual projective components lift to the reduced complex
reference and cover its scheme points by open and closed immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (κ : K →+* ℂ)

omit [NumberField K] in
theorem reduced_projective_component_cover
    [LocallyOfFiniteType (ReducedComplexPEL.reducedComplexPEL M κ).hom] (hM : M.HasProjectiveBallComponents κ) :
    ∃ V : M.ComplexComponent κ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety,
      ∃ f : ∀ c, (V c).toOver ⟶ ReducedComplexPEL.reducedComplexPEL M κ,
        (∀ c, (V c).complexDimension = 2 ∧ IsOpenImmersion (f c).left ∧ IsClosedImmersion (f c).left) ∧
        (∀ c, Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f c ≫ ReducedComplexPEL.reducedComplexPELInclusion M κ)) =
          {x : M.ComplexPoints κ | ConnectedComponents.mk x = c}) ∧
        (⋃ c, Set.range (f c).left) = Set.univ := by
  classical
  choose V hV using hM
  have hf : ∀ c, ∃ f : (V c).toOver ⟶ M.complexFiber κ,
      IsOpenImmersion f.left ∧ IsClosedImmersion f.left ∧
      Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) =
        {x : M.ComplexPoints κ | ConnectedComponents.mk x = c} := fun c => (hV c).1.2
  choose f ho hc hr using hf
  have (c : M.ComplexComponent κ) : IsOpenImmersion (f c).left := ho c
  have (c : M.ComplexComponent κ) : IsClosedImmersion (f c).left := hc c
  have (c : M.ComplexComponent κ) : IsReduced (V c).toOver.left := (V c).carrier_reduced
  let i := ReducedComplexPEL.reducedComplexPELInclusion M κ
  let g := fun c => ClosedLift.reducedClosedOverLift i (f c)
  have hg (c : M.ComplexComponent κ) : g c ≫ i = f c := ClosedLift.reducedClosedOverLift_comp i (f c)
  have (c : M.ComplexComponent κ) : IsOpenImmersion (g c).left := ClosedLift.reducedClosedLift_open i.left (f c).left
  have (c : M.ComplexComponent κ) : IsClosedImmersion (g c).left := ClosedLift.reducedClosedLift_closed i.left (f c).left
  refine ⟨V, g, fun c => ⟨(hV c).1.1, inferInstance, inferInstance⟩,
    (fun c => by rw [hg]; exact hr c), ?_⟩
  apply ComplexPointOpenCover.complex_point_open_images_cover (ReducedComplexPEL.reducedComplexPEL M κ) (fun c => (V c).toOver) g
  intro z
  let c := ConnectedComponents.mk (z ≫ i)
  have hz : z ≫ i ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f c)) := by
    rw [hr c]
    exact rfl
  obtain ⟨y, hy⟩ := hz
  refine ⟨c, y, ?_⟩
  apply (cancel_mono i).mp
  rw [Category.assoc, hg]
  exact hy

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ProjectiveComponentCover

import OAI.RepresentationTheory.Theta.Geometric.CountableUniversalReferenceImages
import OAI.RepresentationTheory.Theta.Geometric.ComponentFormFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.ComponentVarieties

/-! # Countable Reference Ball Images -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The complete literal reference ball is covered by countably many
holomorphic images from the actual projective component dimensions. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA) (hg : D.pel.HasIntegralModelGeometry)

theorem Data.ActiveHeckeThetaData.exists_countable_reference_ball_images :
    ∃ I : Type, Countable I ∧ ∃ j : I → Fin D.pel.componentCount,
      ∃ (O : ∀ i, Set (D.componentVariety hg (j i)).analyticModel)
        (period : ∀ i, (D.componentVariety hg (j i)).analyticModel → Geometry.ComplexBall.PrescribedSignsB.BallChart),
        (∀ i, IsOpen (O i) ∧ DifferentiableOn ℂ (period i) (O i)) ∧
        ∀ a : D.domain, ∃ i,
          (∃ x : (D.componentVariety hg (j i)).analyticSpace,
            x ≫ D.componentComplexInclusion (j i) = D.referenceModuliMap hg a) ∧
          a.val ∈ period i '' O i := by
  have hex (j : Fin D.pel.componentCount) :
      ∃ I : Type, Countable I ∧ ∃ (O : I → Set (D.componentVariety hg j).analyticModel)
        (period : I → (D.componentVariety hg j).analyticModel → Geometry.ComplexBall.PrescribedSignsB.BallChart),
        (∀ i, IsOpen (O i) ∧ DifferentiableOn ℂ (period i) (O i)) ∧
        ∀ a : D.domain,
          (∃ y : (D.componentVariety hg j).analyticSpace, y ≫ D.componentComplexInclusion j =
            D.referenceModuliMap hg a) → ∃ i, a.val ∈ period i '' O i := by
    let X := D.componentVariety hg j
    let : IsIntegral X.toOver.left := X.property
    let : Smooth X.toOver.hom := X.presentation.smooth
    let : SecondCountableTopology (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) := X.analyticSpace_secondCountableTopology
    exact D.exists_countable_universal_reference_images hg (S := X.toOver) (D.componentComplexInclusion j)
  choose I hI O period hO hcover using hex
  let (j : Fin D.pel.componentCount) : Countable (I j) := hI j
  let J := Σ j : Fin D.pel.componentCount, I j
  refine ⟨J, inferInstance, Sigma.fst, fun i => O i.1 i.2, fun i => period i.1 i.2,
    fun i => hO i.1 i.2, ?_⟩
  intro a
  obtain ⟨j, x, hx⟩ := D.exists_component_complex_point hg (D.referenceModuliMap hg a)
  obtain ⟨i, hi⟩ := hcover j a ⟨x, hx⟩
  exact ⟨⟨j, i⟩, ⟨x, hx⟩, hi⟩

end

end OAI.RepresentationTheory.Theta.Geometric

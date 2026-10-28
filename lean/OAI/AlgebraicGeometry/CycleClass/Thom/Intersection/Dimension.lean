import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import OAI.AlgebraicGeometry.Betti.SmoothDimension

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Dimension

noncomputable section

/-! Smooth relative dimensions agree with the actual function-field
dimensions used in ThomClass's codimension grading. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem integral_dimension_of_relativeDimension {X : Scheme} [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) [SmoothOfRelativeDimension n f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = n := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := f) (genericPoint X)
  have htop : U = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      have hy : f (genericPoint X) = y := Subsingleton.elim _ _
      exact hy ▸ e hx
  subst U
  let : Nonempty V := ⟨⟨genericPoint X, hx⟩⟩
  let := Betti.AffineDimension.Realization.sectionBaseAlgebra f V
  change Algebra.IsStandardSmoothOfRelativeDimension n Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) Γ(X, V) at hstd
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ := hstd.out
  let : Finite σ := hσ
  let : Finite ι := hι
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension f]
  exact (Betti.AffineDimension.Realization.affinePresentation_dimension f V hV ι σ P).symm.trans hP

theorem component_dimension (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m P.structureMap]
    (C : irreducibleComponents P.carrier) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (P.componentVariety C).structureMap = m := by
  let : SmoothOfRelativeDimension (0 + m) (P.componentInclusion C ≫ P.structureMap) :=
    smoothOfRelativeDimension_comp 0 m (P.componentInclusion C) P.structureMap
  let : SmoothOfRelativeDimension m (P.componentVariety C).structureMap := by
    simpa only [zero_add, P.componentInclusion_over] using
      (inferInstance : SmoothOfRelativeDimension (0 + m)
        (P.componentInclusion C ≫ P.structureMap))
  exact integral_dimension_of_relativeDimension _ m

theorem supportDimension_add_codimension (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m P.structureMap] (W : IrreducibleCloseds P.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W P.structureMap + P.supportCodimension W = m := by
  let C := P.supportComponent W
  let Z := P.componentSupportPreimage C W (P.support_subset_component W)
  have hW : P.componentSupportImage C Z = W := P.componentSupportImage_preimage C W _
  have h := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension (P.componentVariety C) Z
  rw [← P.componentSupportImage_transcendenceDimension C Z,
    ← P.supportCodimension_componentSupportImage C Z, hW,
    component_dimension P m C] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Dimension

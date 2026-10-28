import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields
import OAI.AlgebraicGeometry.Betti.SmoothDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents

/-! # Grading -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading

noncomputable section

section

/-! The natural-number grading in ProjectionFormula is the actual function-field
dimension grading. This supplies the finite field extension whenever a
proper pushforward generator survives in its specified target degree. -/

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
  have h := CycleClass.Geometric.DimensionCycles.supportDimension_add_dimensionCodimension (P.componentVariety C) Z
  rw [← P.componentSupportImage_transcendenceDimension C Z,
    ← P.supportCodimension_componentSupportImage C Z, hW,
    component_dimension P m C] at h
  exact h

theorem image_dimension_eq_of_grade {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (m n p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (hdeg : p + n = q + m) (W : X.DimensionCycleSupport p)
    (himage : Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val) = q) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W.val) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W.val X.structureMap := by
  have hX := supportDimension_add_codimension X m W.val
  have hY := supportDimension_add_codimension Y n (ProperCycleLinearity.imageSupport f W.val)
  rw [W.property] at hX
  rw [himage] at hY
  omega

/-- The coefficient of a surviving generator is a positive field degree,
rather than the junk value of finrank for an infinite field extension. -/
theorem residueDegree_pos_of_grade {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (m n p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (hdeg : p + n = q + m) (W : X.DimensionCycleSupport p)
    (himage : Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val) = q) :
    0 < f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) :=
  Support.Fields.residueDegree_pos_of_dimension_eq f W.val
    (image_dimension_eq_of_grade f m n p q hdeg W himage)

end

/-! Every point of a Noetherian smooth scheme over the complex
field lies in an integral open with the same smooth relative dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace SmoothIntegralNeighborhood

theorem exists_open {S : Scheme} [NoetherianSpace S] (f : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (r : ℕ)
    [SmoothOfRelativeDimension r f] (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ IsIntegral (U : Scheme) ∧ SmoothOfRelativeDimension r (U.ι ≫ f) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth r f
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents S := irreducibleComponent_mem_irreducibleComponents x
  let U : S.Opens := ⟨C, Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains
    (Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain f) NoetherianSpace.finite_irreducibleComponents hC⟩
  let : IrreducibleSpace (U : Scheme) := isIrreducible_iff_irreducibleSpace.mp hC.1
  let : IsReduced S := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced f
  let : IsReduced (U : Scheme) := inferInstance
  let : IsIntegral (U : Scheme) := isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨U, mem_irreducibleComponent, inferInstance, ?_⟩
  have he : SmoothOfRelativeDimension (0 + r) (U.ι ≫ f) := inferInstance
  rw [Nat.zero_add] at he
  exact he

end SmoothIntegralNeighborhood

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading

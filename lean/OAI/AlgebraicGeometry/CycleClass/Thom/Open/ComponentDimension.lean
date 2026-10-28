import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectiveComponentDimension

/-! # Component Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.ComponentDimension.Constructions

noncomputable section

/-! The dimension of the unique component containing a support can be
computed on any actual integral open subscheme containing that support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem component_dimension_of_open_integral_neighborhood
    (Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (S : IrreducibleCloseds Z.carrier)
    {T : Scheme} [IsIntegral T] (i : T ⟶ Z.carrier) [IsOpenImmersion i]
    (hS : (S : Set Z.carrier) ⊆ Set.range i) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Z.componentVariety (Z.supportComponent S)).structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ Z.structureMap) := by
  let W := Geometric.StratumClosure.integralImageClosure i
  let C := Z.supportComponent W
  have hiC : Set.range i ⊆ C.val := subset_closure.trans (Z.support_subset_component W)
  have hSC : Z.supportComponent S = C := Z.supportComponent_eq_of_subset S C (hS.trans hiC)
  have hfac : Set.range i ⊆ Set.range (Z.componentInclusion C) := by
    rw [Z.componentInclusion_range C]
    exact hiC
  let j := IsOpenImmersion.lift (Z.componentInclusion C) i hfac
  have hj : j ≫ (Z.componentVariety C).structureMap = i ≫ Z.structureMap := by
    rw [← Z.componentInclusion_over C, ← Category.assoc]
    exact congrArg (fun f => f ≫ Z.structureMap) (IsOpenImmersion.lift_fac _ _ hfac)
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion j (Z.componentVariety C).structureMap
  rw [hj] at h
  rw [hSC]
  exact h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.ComponentDimension.Constructions

import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportClosure

/-! # Smooth Support Open Range -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SmoothSupportOpenRange.Constructions

noncomputable section

/-! Exact images of actual smooth support opens inside their regular loci. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

private theorem range_factor {P Q R : Type*} (f : P → Q) (g : Q → R) (h : P → R)
    (hg : Function.Injective g) (hc : g ∘ f = h) : Set.range f = g ⁻¹' Set.range h := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (congrFun hc y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hg ((congrFun hc y).trans hy)⟩

/-- The image of the actual regular-locus factor is the inverse image of
the original smooth open's image under the regular inclusion. -/
theorem smoothOpenToRegular_range {Y S : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [LocallyOfFiniteType Y.hom] [Smooth S.hom]
    (W : IrreducibleCloseds Y.left) (j : S ⟶ Scheme.RegularSupport.Constructions.supportOver Y W) [IsOpenImmersion j.left] :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular (Y := Y) W j)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Scheme.SmoothSupportOpen.Constructions.regularToSupport Y W) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) := by
  apply range_factor _ _ _
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (Scheme.SmoothSupportOpen.Constructions.regularToSupport Y W)).injective
  funext x
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Scheme.SmoothSupportOpen.Constructions.regularToSupport Y W)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular (Y := Y) W j) x) = _
  rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular_inclusion]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SmoothSupportOpenRange.Constructions

import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen

/-! # Intrinsic Graph Image Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic

noncomputable section

/-! The actual graph-ambient coordinates identify the restricted image of every source parametrization with its literal base-coordinate graph. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left] (d : ℕ)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left] (g : X ⟶ Y)
  (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) {L : Type} (r : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

def graphParametrization : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin d) ℂ)) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ∘ r

def graphBase : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ∘ r

def graphCoordinates : L → Fin d → ℂ := Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f ∘ r

def restrictedGraphImage : (graphParametrization d g f r ⁻¹' (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U : Set _)) → U × (Fin d → ℂ) :=
  fun x => IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU ⟨graphParametrization d g f r x.val, x.property⟩

theorem restrictedGraphImage_range_eq_image : Set.range (restrictedGraphImage j d U hU g f r) =
    IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU '' ((Subtype.val : IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U → _) ⁻¹'
      Set.range (graphParametrization d g f r)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨graphParametrization d g f r x.val, x.property⟩, ⟨x.val, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx⟩, rfl⟩
    have hxA : graphParametrization d g f r x ∈ IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U := hx.symm ▸ y.property
    exact ⟨⟨x, hxA⟩, congrArg (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU) (Subtype.ext hx)⟩

theorem restrictedGraphImage_range : Set.range (restrictedGraphImage j d U hU g f r) =
    Set.range (GraphBaseRestriction.Constructions.restrictedGraph (graphBase j g r) (graphCoordinates d f r) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have hx : graphBase j g r x.val ∈ U := (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphPoint_mem_ambientOpen j d U g f (r x.val)).mp x.property
    refine ⟨⟨x.val, hx⟩, ?_⟩
    exact (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_graph j d U hU g f (r x.val) hx).symm
  · rintro ⟨x, rfl⟩
    have hx : graphParametrization d g f r x.val ∈ IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U :=
      (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphPoint_mem_ambientOpen j d U g f (r x.val)).mpr x.property
    refine ⟨⟨x.val, hx⟩, ?_⟩
    exact IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_graph j d U hU g f (r x.val) x.property

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic

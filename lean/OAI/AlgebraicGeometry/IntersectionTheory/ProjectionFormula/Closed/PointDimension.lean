import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntermediateSupports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra

/-! # Point Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointDimension

noncomputable section

/-! Closed points of a smooth projective scheme have full local
dimension. Their first-order data consequently have dimension m+1. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem support_dimension {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed {x}) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = 0 := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.affineOpens := ⟨U, hU⟩
  let W : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  let : Nonempty (Foundations.Scheme.SupportAffineQuotient.supportAffineOpen W V) := (Foundations.Scheme.SupportAffineInclusion.supportAffineOpen_nonempty_iff W V).mpr
    ⟨x, subset_closure (Set.mem_singleton x), hxU⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let : Algebra.FiniteType ℂ Γ(X, U) := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let := Foundations.Scheme.SupportAffineQuotient.supportAffineQuotientScalarAlgebra W f V
  have hmax : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).ideal V).IsMaximal := by
    rw [DivisorClass.Chern.SupportCodimension.Construction.pointClosure_affineIdeal x V hxU]
    exact hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
  let := hmax
  let : Field (Foundations.Scheme.SupportAffineQuotient.supportAffineQuotient W V) := Ideal.Quotient.field _
  let : Algebra.FiniteType ℂ (Foundations.Scheme.SupportAffineQuotient.supportAffineQuotient W V) := by infer_instance
  let : Module.Finite ℂ (Foundations.Scheme.SupportAffineQuotient.supportAffineQuotient W V) :=
    finite_of_finite_type_of_isJacobsonRing ℂ (Foundations.Scheme.SupportAffineQuotient.supportAffineQuotient W V)
  have : Algebra.IsAlgebraic ℂ (Foundations.Scheme.SupportAffineQuotient.supportAffineQuotient W V) := by infer_instance
  rw [Foundations.Scheme.SupportDimension.supportTranscendenceDimension_eq_affineQuotient W f V, trdeg_eq_zero]
  simp

theorem codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (x : X.carrier) (hx : IsClosed {x}) :
    X.supportCodimension (irreducibleSetEquivPoints.symm x) = m := by
  have h := Grading.supportDimension_add_codimension X m (irreducibleSetEquivPoints.symm x)
  rwa [support_dimension X.structureMap x hx, zero_add] at h

theorem coheight (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (x : X.carrier) (hx : IsClosed {x}) :
    Order.coheight x = m := by
  have h := IntermediateSupports.support_coheight X m m
    ⟨irreducibleSetEquivPoints.symm x, codimension X m x hx⟩
  simpa only [CycleClass.Thom.IntersectionGeometry.supportPoint, irreducibleSetEquivPoints.apply_symm_apply] using h

theorem point_jet_dimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier) (hp : p ≫ X.structureMap = 𝟙 _) :
    letI := Stalk.PointAlgebra.scalarAlgebra X.structureMap (p (IsLocalRing.closedPoint ℂ))
    Module.finrank ℂ (ℂ × (AugmentedCotangent.ideal
      (Stalk.PointAlgebra.evaluation X.structureMap p hp)).Cotangent) = m + 1 := by
  apply Stalk.PointAlgebra.jet_dimension X.structureMap m p hp
  apply PointDimension.coheight X m
  exact ((pointEquivClosedPoint X.structureMap) ⟨p, hp⟩).property

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointDimension

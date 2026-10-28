import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.LocalMultiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Dimension

/-! # Multiplicity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Multiplicity

noncomputable section

section

/-! ThomClass's actual projective intersection multiplicity of the cone
and a closed embedded integral scheme is one at an etale projection point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
  (hL : LinearIndependent ℂ L) {Z : Scheme} [IsIntegral Z]
  (i : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) [IsClosedImmersion i]
  (hi : ∀ z, i z ∈ Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L))

omit [IsIntegral Z] [IsClosedImmersion i] in
theorem point_mem_cone (z : Z) :
    i z ∈ (Projective.ConeSupport.support L hL (Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi z) :
      Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := by
  let x := LocalMultiplicity.lift L i hi z
  have hx := StalkIdeal.mem_of_map L hL
    (Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi z) x rfl
  have hm := (StalkIdeal.mem_iff L hL _ x).mp hx
  have he := congrArg (fun g : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n => g z) (LocalMultiplicity.lift_fac L i hi)
  exact Eq.mp (congrArg (fun y : Foundations.Scheme.ProjectiveSpace.projectiveSpace n => y ∈
    (Projective.ConeSupport.support L hL (Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi z) : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))) he) hm

omit [IsClosedImmersion i] in
theorem point_mem_image (z : Z) : i z ∈ (Closed.ImmersionSupport.support i : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := by
  change i z ∈ (CycleClass.Geometric.StratumClosure.integralImageClosure i : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
  rw [CycleClass.Geometric.StratumClosure.integralImageClosure_coe]
  exact subset_closure (Set.mem_range_self z)

theorem multiplicity_one
    (U : Z.Opens) [Etale (U.ι ≫ Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi)]
    (z : Z) (hz : z ∈ U)
    (C : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation n).carrier)
    (hC : CycleClass.Thom.IntersectionGeometry.supportPoint C = i z) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity (Projective.Dimension.SpacePresentation.presentation n)
      (Projective.ConeSupport.support L hL (Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi z))
      (Closed.ImmersionSupport.support i) C = 1 := by
  have hA := point_mem_cone L hL i hi z
  have hB := point_mem_image i z
  let A : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation n).carrier :=
    Projective.ConeSupport.support L hL (Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) i hi z)
  let B : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation n).carrier :=
    Closed.ImmersionSupport.support i
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈
      (A : Set (Projective.Dimension.SpacePresentation.presentation n).carrier) ∩
      (B : Set (Projective.Dimension.SpacePresentation.presentation n).carrier) := by
    rw [hC]
    exact ⟨hA, hB⟩
  change CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity (Projective.Dimension.SpacePresentation.presentation n) A B C = 1
  rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left hx]
  have he (k : ℕ) := Open.SupportTor.localTorLength_congr_point
    (Projective.Dimension.SpacePresentation.presentation n).carrier A B hC hx.1 hx.2 hA hB k
  simp_rw [he]
  exact LocalMultiplicity.euler_one L hL i hi U z hz hA hB n

end

/-! The original irreducible support occurs with coefficient one
in the cone intersection whenever the projection is etale near one of
its points. The coefficient is ThomClass's native intersection multiplicity. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace IntegralProjection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
  (W : IrreducibleCloseds X.carrier)

def imageSupport : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier :=
  irreducibleSetEquivPoints.symm (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint W))

theorem image_point : CycleClass.Thom.IntersectionGeometry.supportPoint (imageSupport X W) = X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint W) :=
  irreducibleSetEquivPoints.apply_symm_apply _

theorem multiplicity_one [IsIntegral X.carrier]
    (U : X.carrier.Opens) [Etale (U.ι ≫ Projection.FiniteProjective.FromForms.map X m L h)]
    (x : X.carrier) (hxW : x ∈ (W : Set X.carrier)) (hxU : x ∈ U) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity (Projective.Dimension.SpacePresentation.presentation X.ambientDimension)
      (Projective.ConeSupport.support L hL (Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W)))
      (Closed.ImmersionSupport.support X.embedding) (imageSupport X W) = 1 := by
  have hη : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ U :=
    ((W.isIrreducible.isGenericPoint_genericPoint W.isClosed).specializes hxW).mem_open U.isOpen hxU
  let : Etale (U.ι ≫ Projective.ProjectionRestriction.projection
      (Projective.ConeSupport.coordinates L) X.embedding (Projection.FiniteProjective.FromForms.in_domain X m L h)) := by
    change Etale (U.ι ≫ Projection.FiniteProjective.FromForms.map X m L h)
    infer_instance
  exact Multiplicity.multiplicity_one L hL X.embedding
    (Projection.FiniteProjective.FromForms.in_domain X m L h) U (CycleClass.Thom.IntersectionGeometry.supportPoint W) hη (imageSupport X W) (image_point X W)

end IntegralProjection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Multiplicity

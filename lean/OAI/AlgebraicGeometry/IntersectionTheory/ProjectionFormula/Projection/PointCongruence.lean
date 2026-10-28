import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DefinedPair
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointIncidenceImage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointIdeal

/-! # Point Congruence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointCongruence

noncomputable section

section

/-! The finite projections of two reduced supports compute the
actual closed incidence locus through the projections of their pair scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace SupportData

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)

def NoBase (W : IrreducibleCloseds X.carrier) : Prop :=
  ∀ x ∈ (W : Set X.carrier), ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal

theorem in_domain (W : IrreducibleCloseds X.carrier) (hW : NoBase X k L W) (w : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :
    (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.embedding) w ∈ Projective.BasicOpen.RationalProjection.domain (FiniteProjective.FromForms.coordinates X k L) := by
  apply (PartialLinear.Projection.mem_domain X k L (CycleClass.Geometric.GenericPoint.reducedSupportι W w)).mpr
  apply hW
  rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact Set.mem_range_self w

def projection (W : IrreducibleCloseds X.carrier) (hW : NoBase X k L W) :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace k :=
  Projective.ProjectionRestriction.projection (FiniteProjective.FromForms.coordinates X k L)
    (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.embedding) (in_domain X k L W hW)

instance finite (W : IrreducibleCloseds X.carrier) (hW : NoBase X k L W) :
    IsFinite (projection X k L W hW) :=
  Projective.Finite.Projection.isFinite _ _ _ (FiniteProjective.FromForms.constants X k L)

variable (W Z : IrreducibleCloseds X.carrier) (hW : NoBase X k L W) (hZ : NoBase X k L Z)

include hW in
theorem first_domain (a : Support.Pair.space X W Z) : (Support.Pair.first X W Z).left a ∈ PartialLinear.Projection.domain X k L :=
  (PartialLinear.Projection.mem_domain X k L _).mpr (hW _ (DisjointIncidenceImage.first_mem X W Z a))

include hZ in
theorem second_domain (a : Support.Pair.space X W Z) : (Support.Pair.second X W Z).left a ∈ PartialLinear.Projection.domain X k L :=
  (PartialLinear.Projection.mem_domain X k L _).mpr (hZ _ (DisjointIncidenceImage.second_mem X W Z a))

theorem first_point (a : Support.Pair.space X W Z) :
    (DefinedPair.Projection.projection X k L (Support.Pair.first X W Z) (first_domain X k L W Z hW)).left a =
      projection X k L W hW
        (pullback.fst (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) a) := by
  apply ProjectiveSpectrum.ext
  exact (PointIdeal.ideal (FiniteProjective.FromForms.coordinates X k L)
    ((Support.Pair.first X W Z).left ≫ X.embedding) (first_domain X k L W Z hW)
    (FiniteProjective.FromForms.constants X k L) a).trans
    (PointIdeal.ideal (FiniteProjective.FromForms.coordinates X k L)
      (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.embedding) (in_domain X k L W hW)
      (FiniteProjective.FromForms.constants X k L) _).symm

theorem second_point (a : Support.Pair.space X W Z) :
    (DefinedPair.Projection.projection X k L (Support.Pair.second X W Z) (second_domain X k L W Z hZ)).left a =
      projection X k L Z hZ
        (pullback.snd (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) a) := by
  apply ProjectiveSpectrum.ext
  exact (PointIdeal.ideal (FiniteProjective.FromForms.coordinates X k L)
    ((Support.Pair.second X W Z).left ≫ X.embedding) (second_domain X k L W Z hZ)
    (FiniteProjective.FromForms.constants X k L) a).trans
    (PointIdeal.ideal (FiniteProjective.FromForms.coordinates X k L)
      (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.embedding) (in_domain X k L Z hZ)
      (FiniteProjective.FromForms.constants X k L) _).symm

theorem mem_incidence (a : Support.Pair.space X W Z) (ha : IsClosed ({a} : Set (Support.Pair.space X W Z))) :
    a ∈ Support.PairIncidenceStep.incidence X W Z k L ↔
      projection X k L W hW (pullback.fst (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) a) =
        projection X k L Z hZ (pullback.snd (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) a) := by
  have he := DefinedPair.Projection.mem_iff_closed X k L (Support.Pair.first X W Z) (Support.Pair.second X W Z)
    (first_domain X k L W Z hW) (second_domain X k L W Z hZ) a ha
  rw [first_point, second_point] at he
  exact he

end SupportData

end

/-! Projected points depend only on their actual ambient projective
point, including passage to a native reduced support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem point {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    (hC : ∀ c : ℂ, f (MvPolynomial.C c) = MvPolynomial.C c)
    {S T : Scheme} (i : S ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (j : T ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (hi : ∀ x, i x ∈ Projective.BasicOpen.RationalProjection.domain f)
    (hj : ∀ y, j y ∈ Projective.BasicOpen.RationalProjection.domain f)
    (x : S) (y : T) (hxy : i x = j y) :
    Projective.ProjectionRestriction.projection f i hi x =
      Projective.ProjectionRestriction.projection f j hj y := by
  apply ProjectiveSpectrum.ext
  exact (PointIdeal.ideal f i hi hC x).trans
    ((congrArg (fun p : Foundations.Scheme.ProjectiveSpace.projectiveSpace n => p.asHomogeneousIdeal.comap f) hxy).trans
      (PointIdeal.ideal f j hj hC y).symm)

theorem support_point (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
    (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (W : IrreducibleCloseds X.carrier) (hW : SupportData.NoBase X k L W)
    {T : Scheme} (i : T ⟶ X.carrier)
    (hi : ∀ y, (i ≫ X.embedding) y ∈ Projective.BasicOpen.RationalProjection.domain (FiniteProjective.FromForms.coordinates X k L))
    (x : T) (hx : i x ∈ (W : Set X.carrier)) :
    SupportData.projection X k L W hW (CycleClass.Thom.IntersectionGeometry.supportPreimage W (i x) hx) =
      Projective.ProjectionRestriction.projection (FiniteProjective.FromForms.coordinates X k L) (i ≫ X.embedding) hi x :=
  point (FiniteProjective.FromForms.coordinates X k L) (FiniteProjective.FromForms.constants X k L)
    (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.embedding) (i ≫ X.embedding) (SupportData.in_domain X k L W hW) hi
    (CycleClass.Thom.IntersectionGeometry.supportPreimage W (i x) hx) x (congrArg X.embedding (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W (i x) hx))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointCongruence

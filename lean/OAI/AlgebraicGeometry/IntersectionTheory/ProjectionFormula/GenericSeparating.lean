import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairClosedPoints

/-! # Generic Separating -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GenericSeparating

noncomputable section

section

/-! A negative expected off-diagonal incidence dimension forces
singleton fibers on positive-codimension supports at the selected points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace IncidenceFiberSeparation

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite.Projection

theorem subset_of_dimension {S : Scheme} (f : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I F : Closeds S) (m d : ℕ)
    (hd : d < m)
    (hI : ∀ C : IrreducibleCloseds S, (C : Set S) ⊆ I → ¬ (C : Set S) ⊆ F →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C f + m ≤ d) : I ≤ F := by
  intro x hx
  by_contra hn
  let C : IrreducibleCloseds S := irreducibleSetEquivPoints.symm x
  have hxC : x ∈ C := subset_closure (Set.mem_singleton x)
  have hC : (C : Set S) ⊆ I := closure_minimal (Set.singleton_subset_iff.mpr hx) I.isClosed
  have hb := hI C hC (fun h => hn (h hxC))
  omega

theorem fiber_eq (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    (π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) [IsFinite π.left]
    (W : IrreducibleCloseds X.carrier) (x : X.carrier) (hx : IsClosed {x})
    (hI : Generic.Finite.Projection.coincidence X W (irreducibleSetEquivPoints.symm x) π ≤
      Support.PairIncidenceStep.diagonal X W (irreducibleSetEquivPoints.symm x))
    (y : X.carrier) (hy : y ∈ W) (he : π.left y = π.left x) : y = x := by
  have hπx : IsClosed ({π.left x} : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace m)) := by
    simpa only [Set.image_singleton] using π.left.isClosedMap _ hx
  have hyc : IsClosed ({y} : Set X.carrier) := Closed.FiberPoints.closed π.left y (he.symm ▸ hπx)
  obtain ⟨a, ha, hay, hax⟩ := Support.PairClosedPoints.exists_pair X W
    (irreducibleSetEquivPoints.symm x) y x hyc hx hy (subset_closure (Set.mem_singleton x))
  have heq : (Support.Pair.first X W (irreducibleSetEquivPoints.symm x) ≫ π).left a =
      (Support.Pair.second X W (irreducibleSetEquivPoints.symm x) ≫ π).left a := by
    change π.left ((Support.Pair.first X W (irreducibleSetEquivPoints.symm x)).left a) =
      π.left ((Support.Pair.second X W (irreducibleSetEquivPoints.symm x)).left a)
    rw [hay, hax]
    exact he
  have haI : a ∈ Generic.Finite.Projection.coincidence X W (irreducibleSetEquivPoints.symm x) π :=
    Closed.Equalizer.mem_of_closed (Support.Pair.first X W (irreducibleSetEquivPoints.symm x) ≫ π)
      (Support.Pair.second X W (irreducibleSetEquivPoints.symm x) ≫ π) a ha heq
  have haD := hI haI
  have he' := Closed.Equalizer.eq_of_mem (Support.Pair.first X W (irreducibleSetEquivPoints.symm x))
    (Support.Pair.second X W (irreducibleSetEquivPoints.symm x)) a haD
  exact hay.symm.trans (he'.trans hax)

end IncidenceFiberSeparation

end

/-! Generic incidence bounds and singleton support fibers hold for
the same finite projection, with etale neighborhoods at the chosen points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite.Projection

theorem exists_projection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {τ ι : Type} [Finite τ] [Finite ι] (W Z : τ → IrreducibleCloseds X.carrier)
    (V : ι → IrreducibleCloseds X.carrier) (hV : ∀ j, 1 ≤ X.supportCodimension (V j))
    (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j}) :
    ∃ π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m), IsFinite π.left ∧
      (∀ j, (∃ U : X.carrier.Opens, x j ∈ U ∧ Etale (U.ι ≫ π.left)) ∧
        ∀ y ∈ V j, π.left y = π.left (x j) → y = x j) ∧
      ∀ t, ∀ C : IrreducibleCloseds (Support.Pair.space X (W t) (Z t)),
        (C : Set (Support.Pair.space X (W t) (Z t))) ⊆ Generic.Finite.Projection.coincidence X (W t) (Z t) π →
        ¬ (C : Set (Support.Pair.space X (W t) (Z t))) ⊆ Support.PairIncidenceStep.diagonal X (W t) (Z t) →
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X (W t) (Z t)) + m ≤
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap := by
  let A : τ ⊕ ι → IrreducibleCloseds X.carrier := Sum.elim W V
  let B : τ ⊕ ι → IrreducibleCloseds X.carrier :=
    Sum.elim Z (fun j => irreducibleSetEquivPoints.symm (x j))
  obtain ⟨π, hfinite, hetale, hI⟩ := Generic.Finite.Projection.exists_closed_points X m A B x hx
  let := hfinite
  refine ⟨π, hfinite, ?_, fun t => hI (Sum.inl t)⟩
  intro j
  refine ⟨hetale j, ?_⟩
  have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (V j) X.structureMap +
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (x j)) X.structureMap < m := by
    rw [Closed.PointDimension.support_dimension X.structureMap (x j) (hx j)]
    have he := Grading.supportDimension_add_codimension X m (V j)
    have hv := hV j
    omega
  have hs := IncidenceFiberSeparation.subset_of_dimension (Support.Pair.base X (V j) (irreducibleSetEquivPoints.symm (x j)))
    (Generic.Finite.Projection.coincidence X (V j) (irreducibleSetEquivPoints.symm (x j)) π)
    (Support.PairIncidenceStep.diagonal X (V j) (irreducibleSetEquivPoints.symm (x j)))
    m _ hd (hI (Sum.inr j))
  exact IncidenceFiberSeparation.fiber_eq X m π (V j) (x j) (hx j) hs

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GenericSeparating

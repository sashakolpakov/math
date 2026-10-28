import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Unions

/-! # Span Index -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.SpanIndex

noncomputable section

/-! A finite index type records every pair of intersection inclusions with a common target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

abbrev finiteIntersectionSpanIndex :=
  {p : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X × HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X × HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X //
    p.1.val ⊆ p.2.1.val ∧ p.1.val ⊆ p.2.2.val}

instance finiteIntersectionSpanIndex_finite : Finite (finiteIntersectionSpanIndex X) := inferInstance

abbrev finiteIntersectionSpanBase (j : finiteIntersectionSpanIndex X) : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X :=
  j.val.1

abbrev finiteIntersectionSpanLeft (j : finiteIntersectionSpanIndex X) : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X :=
  j.val.2.1

abbrev finiteIntersectionSpanRight (j : finiteIntersectionSpanIndex X) : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X :=
  j.val.2.2

abbrev finiteIntersectionSpanUnion (j : finiteIntersectionSpanIndex X) : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X :=
  Unions.finiteIntersectionUnion X (finiteIntersectionSpanLeft X j) (finiteIntersectionSpanRight X j)

theorem finiteIntersectionSpan_left (j : finiteIntersectionSpanIndex X) :
    (finiteIntersectionSpanBase X j).val ⊆ (finiteIntersectionSpanLeft X j).val := j.property.1

theorem finiteIntersectionSpan_right (j : finiteIntersectionSpanIndex X) :
    (finiteIntersectionSpanBase X j).val ⊆ (finiteIntersectionSpanRight X j).val := j.property.2

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.SpanIndex

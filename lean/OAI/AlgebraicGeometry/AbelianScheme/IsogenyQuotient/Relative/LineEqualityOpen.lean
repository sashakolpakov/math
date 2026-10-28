import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineDifference
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.TraceTriviality

/-! # Line Equality Open -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.LineEqualityOpen.Construction

noncomputable section

/-! For two lines with isomorphic pullbacks along the isogeny, an
actual open equality locus contains every characteristic-zero fiber
on which their classes agree. The equality on the open is proved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S}
  [IsProper B.hom] (f : A ⟶ B)
  [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]
  (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
  (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))

def lineEqualityOpen : S.Opens :=
  TraceTriviality.Construction.traceTrivialityOpen f (LineDifference.Construction.lineDifference L M) (LineDifference.Construction.lineDifferencePullbackFrame f.left L M h).hom

theorem lineEqualityOpen_class_eq :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.hom ⁻¹ᵁ lineEqualityOpen f L M h).ι (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.hom ⁻¹ᵁ lineEqualityOpen f L M h).ι (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
  apply (LineDifference.Construction.lineDifference_pullback_trivial_iff _ L M).mp
  exact Quotient.sound (TraceTriviality.Construction.traceTrivialityOpen_line_trivial f (LineDifference.Construction.lineDifference L M)
    (LineDifference.Construction.lineDifferencePullbackFrame f.left L M h).hom)

theorem lineEqualityOpen_contains_field_fiber
    [GrpObj A] [GrpObj B] [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] [Surjective f.left]
    {k : Type u} [Field k] [CharZero k] (t : Spec (.of k) ⟶ S)
    (ht : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst B.hom t) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst B.hom t) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
    (s : Spec (.of k)) : t s ∈ lineEqualityOpen f L M h :=
  TraceTriviality.Construction.traceTrivialityOpen_contains_trivial_field_fiber f (LineDifference.Construction.lineDifference L M)
    (LineDifference.Construction.lineDifferencePullbackFrame f.left L M h).hom t
    (LineDifference.Construction.lineDifferencePullbackFrame (pullback.fst B.hom t) L M ht) s

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.LineEqualityOpen.Construction

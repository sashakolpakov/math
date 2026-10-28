import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.LineEqualityOpen

/-! # Line Equality Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEqualityBaseChange.Construction

noncomputable section

/-! The relative line equality neighborhood can be tested on any
actual Cartesian presentation of the chosen field fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem pullbackClass_injective_of_section {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    Function.Injective (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f) := by
  intro a b h
  have H := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass s) h
  simpa only [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hs, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] using H

theorem lineEqualityOpen_contains_field_isPullback
    {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
    (f : A ⟶ B) [IsFinite f.left] [Flat f.left] [Surjective f.left]
    [LocallyOfFinitePresentation f.left] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
    {k : Type u} [Field k] [CharZero k] (t : Spec (.of k) ⟶ S)
    {Y : Scheme.{u}} (a : Y ⟶ B.left) (r : Y ⟶ Spec (.of k))
    (H : IsPullback a r B.hom t)
    (ht : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
    (s : Spec (.of k)) : t s ∈ Relative.LineEqualityOpen.Construction.lineEqualityOpen f L M h := by
  apply Relative.LineEqualityOpen.Construction.lineEqualityOpen_contains_field_fiber f L M h t _ s
  apply pullbackClass_injective_of_section H.isoPullback.hom H.isoPullback.inv H.isoPullback.inv_hom_id
  simpa only [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, H.isoPullback_hom_fst] using ht

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEqualityBaseChange.Construction

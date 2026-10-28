import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceTrivialLineFrame
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperFrameNeighborhood
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalIsomorphismsIs

/-! # Trace Triviality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.TraceTriviality.Construction

noncomputable section

/-! A line trivialized by a finite-flat map of proper smooth connected
groups becomes trivial near any characteristic-zero fiber on which it
is trivial. The neighborhood and its frame come from the actual trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (f : A ⟶ B) [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
  (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ (L.pullback f.left).sheaf) [IsIso z]

omit [GrpObj A] [GrpObj B] [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] [Surjective f.left] [IsIso z] in
def traceTrivialityOpen : S.Opens := ProperFrameNeighborhood.Construction.sectionFrameNeighborhood B.hom (GlobalTraceSection.Construction.finiteFlatTraceSection f.left L z)

omit [GrpObj A] [GrpObj B] [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] [Surjective f.left] [IsIso z] in
theorem traceTrivialityOpen_line_trivial :
    Nonempty ((L.pullback (B.hom ⁻¹ᵁ traceTrivialityOpen f L z).ι).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (B.hom ⁻¹ᵁ traceTrivialityOpen f L z).toScheme) := by
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (B.hom ⁻¹ᵁ traceTrivialityOpen f L z).ι
      (GlobalTraceSection.Construction.finiteFlatTraceSection f.left L z)) :=
    ProperFrameNeighborhood.Construction.sectionFrameNeighborhood_isIso B.hom (GlobalTraceSection.Construction.finiteFlatTraceSection f.left L z)
  exact ⟨(asIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (B.hom ⁻¹ᵁ traceTrivialityOpen f L z).ι
    (GlobalTraceSection.Construction.finiteFlatTraceSection f.left L z))).symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem traceTrivialityOpen_contains_trivial_field_fiber
    {k : Type u} [Field k] [CharZero k] (t : Spec (.of k) ⟶ S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback B.hom t) ≅ (L.pullback (pullback.fst B.hom t)).sheaf)
    (s : Spec (.of k)) : t s ∈ traceTrivialityOpen f L z := by
  let A' := (Over.pullback t).obj A
  let B' := (Over.pullback t).obj B
  let f' := (Over.pullback t).map f
  have : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : Smooth A'.hom := inferInstanceAs (Smooth (pullback.snd A.hom t))
  have : GeometricallyConnected A'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t))
  have : IsProper B'.hom := inferInstanceAs (IsProper (pullback.snd B.hom t))
  have : Smooth B'.hom := inferInstanceAs (Smooth (pullback.snd B.hom t))
  have : GeometricallyConnected B'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd B.hom t))
  have : IsFinite f'.left := MorphismProperty.overPullbackMap (P := @IsFinite) t _ inferInstance
  have : Flat f'.left := MorphismProperty.overPullbackMap (P := @Flat) t _ inferInstance
  have : Surjective f'.left := MorphismProperty.overPullbackMap (P := @Surjective) t _ inferInstance
  have : LocallyOfFinitePresentation f'.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) t _ inferInstance
  let h := CartierDuality.LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback t f
  let L' := L.pullback (pullback.fst B.hom t)
  let z' := SquareSectionComposition.Construction.pullbackSquareSection f.left f'.left (pullback.fst A.hom t) (pullback.fst B.hom t) h.w z
  have : IsIso z' := by
    change IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst A.hom t) z ≫
      (PullbackSectionSquares.Construction.sectionPullbackSquareIso f.left f'.left (pullback.fst A.hom t)
        (pullback.fst B.hom t) h.w L.sheaf).hom)
    infer_instance
  have : IsIso (GlobalTraceSection.Construction.finiteFlatTraceSection f'.left L' z') :=
    TraceTrivialLineFrame.Construction.properGroupTraceSection_isIso_of_trivial_line f' L' e z'
  have ht := GlobalTraceBaseChange.Construction.finiteFlatTraceSection_baseChange f.left f'.left
    (pullback.fst A.hom t) (pullback.fst B.hom t) h L z
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst B.hom t) (GlobalTraceSection.Construction.finiteFlatTraceSection f.left L z)) := by
    rw [ht]
    infer_instance
  exact ProperFrameNeighborhood.Construction.mem_sectionFrameNeighborhood_of_baseChange_isIso B.hom L
    (GlobalTraceSection.Construction.finiteFlatTraceSection f.left L z) t (t s) ⟨s, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.TraceTriviality.Construction

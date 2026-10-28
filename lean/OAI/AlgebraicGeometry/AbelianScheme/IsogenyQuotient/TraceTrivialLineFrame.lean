import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TracePullbackFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundlePullbackNormalization
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

/-! # Trace Trivial Line Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceTrivialLineFrame.Construction

noncomputable section

/-! Over a characteristic-zero field, a frame on the finite cover of
a trivial line has a trace which is a frame. Global functions provide
the comparison with a pulled-back frame only on this field fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false in
theorem exists_frame_pullback_eq_of_appTop_isIso
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsIso q.appTop]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ L.sheaf)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) [IsIso z] :
    ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf, IsIso s ∧ AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q s = z := by
  obtain ⟨a, ha, _⟩ := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.existsUnique_iso_with_pullback q
    (ConcreteCategory.bijective_of_isIso q.appTop) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial Y) L ⟨e⟩
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q ≪≫ asIso z)
  refine ⟨a.hom, a.isIso_hom, ?_⟩
  change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).inv ≫ (Scheme.Modules.pullback q).map a.hom = z
  rw [ha]
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).inv_hom_id_assoc z

theorem finiteFlatTraceSection_isIso_of_trivial_line
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q] [IsIso q.appTop]
    {k : Type u} [Field k] [CharZero k] (p : Y ⟶ Spec (.of k))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ L.sheaf)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) [IsIso z] :
    IsIso (GlobalTraceSection.Construction.finiteFlatTraceSection q L z) := by
  obtain ⟨s, hs, hz⟩ := exists_frame_pullback_eq_of_appTop_isIso q L e z
  have : IsIso s := hs
  rw [← hz]
  exact TracePullbackFrame.Construction.finiteFlatTraceSection_pullback_frame_isIso q L p s

theorem properGroupMap_appTop_isIso
    {k : Type u} [Field k] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
    (f : A ⟶ B) : IsIso f.left.appTop := by
  have : IsIso A.hom.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso A
  have : IsIso B.hom.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso B
  have h : IsIso (B.hom.appTop ≫ f.left.appTop) := by
    rw [← Scheme.Hom.comp_appTop, f.w]
    infer_instance
  exact (isIso_comp_left_iff B.hom.appTop f.left.appTop).mp h

theorem properGroupTraceSection_isIso_of_trivial_line
    {k : Type u} [Field k] [CharZero k] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
    (f : A ⟶ B) [IsFinite f.left] [Flat f.left] [Surjective f.left]
    [LocallyOfFinitePresentation f.left] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left ≅ L.sheaf)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ (L.pullback f.left).sheaf) [IsIso z] :
    IsIso (GlobalTraceSection.Construction.finiteFlatTraceSection f.left L z) := by
  have : IsIso f.left.appTop := properGroupMap_appTop_isIso f
  exact finiteFlatTraceSection_isIso_of_trivial_line f.left B.hom L e z

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceTrivialLineFrame.Construction

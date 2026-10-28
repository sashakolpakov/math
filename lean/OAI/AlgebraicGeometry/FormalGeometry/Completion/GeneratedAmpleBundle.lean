import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Projectivity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SectionDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteMorphism

/-! # Generated Ample Bundle -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! A symmetric ample bundle with actual generating global section frames
is obtained from the native proper group by taking a positive tensor power. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

universe u

theorem Frame.SectionDetection.Construction.HasFrameSections.pullback {X Y : Scheme.{u}} {M : Y.Modules}
    (h : Frame.SectionDetection.Construction.HasFrameSections M) (f : X ⟶ Y) :
    Frame.SectionDetection.Construction.HasFrameSections ((Scheme.Modules.pullback f).obj M) := by
  intro x
  obtain ⟨s, hs⟩ := h (f x)
  exact ⟨AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s,
    (Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f h.lineBundle s).symm ▸ hs⟩

theorem GeneratedAmpleBundle.Construction.ample_exists_power_hasFrameSections {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ Frame.SectionDetection.Construction.HasFrameSections (L.tensorPower n).sheaf := by
  obtain ⟨n, hn, r, s, hs, _⟩ := hL.projective_section_family
  refine ⟨n, hn, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hs x
  exact ⟨s i, hi⟩

theorem GeneratedAmpleBundle.Construction.exists_symmetric_generated_ample_lineBundle
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] :
    ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left, L.IsAmple ∧ Frame.SectionDetection.Construction.HasFrameSections L.sheaf ∧
      Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf) := by
  obtain ⟨L, hL, hs⟩ := Geometric.Projectivity.Construction.exists_symmetric_ample_lineBundle A
  obtain ⟨n, hn, hg⟩ := GeneratedAmpleBundle.Construction.ample_exists_power_hasFrameSections L hL
  refine ⟨L.tensorPower n, hL.tensorPower n hn, hg, ?_⟩
  have hb : Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (GrpObj.inv (X := A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := Quotient.sound hs
  have hp : Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (GrpObj.inv (X := A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n) := by
    simp only [Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow, map_pow, hb]
  exact Quotient.exact hp

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion

import OAI.RepresentationTheory.Theta.Geometric.TrivialSectionFrameReflection
import OAI.RepresentationTheory.Theta.Geometric.Local.BaseFrameExtension
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback

/-! # Closed Fiber Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.ClosedFiberFrames

noncomputable section

/-! A normalized section is a frame on a trivial closed fiber whose
axis detects global functions; properness then extends the frame over
the local base. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback.Construction

universe u

theorem rigidifiedSection_endValue {X T : Scheme.{u}} (b : T ⟶ X)
    (M : X.Modules) (r : (Scheme.Modules.pullback b).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T)
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b s ≫ r.hom) =
      r.hom.app ⊤ (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b M (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s)) := by
  change r.hom.app ⊤ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback b).obj M)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b s)) = _
  rw [AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_pullback]

theorem normalizedTrivialSection_isIso {X T : Scheme.{u}} (b : T ⟶ X) [IsIso b.appTop]
    (M : X.Modules) (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (r : (Scheme.Modules.pullback b).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T)
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (h : r.hom.app ⊤ (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b M (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s)) =
      (1 : Γ(T, ⊤))) : IsIso s := by
  have hu : IsUnit (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b s ≫ r.hom)) := by
    rw [rigidifiedSection_endValue, h]
    exact isUnit_one
  have hc : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b s ≫ r.hom) :=
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff _).mpr hu
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b s) := (isIso_comp_right_iff _ r.hom).mp hc
  exact TrivialSectionFrameReflection.trivialSection_isIso_of_pullback b e s

theorem normalizedClosedFiberSection_isIso
    {R : Type u} [CommRing R] [IsLocalRing R] {X T : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) [IsProper π] (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)
    (b : T ⟶ π.fiber (IsLocalRing.closedPoint R)) [IsIso b.appTop]
    (e : (Scheme.Modules.pullback (π.fiberι (IsLocalRing.closedPoint R))).obj L.sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (IsLocalRing.closedPoint R)))
    (r : (Scheme.Modules.pullback b).obj
      ((Scheme.Modules.pullback (π.fiberι (IsLocalRing.closedPoint R))).obj L.sheaf) ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T)
    (h : r.hom.app ⊤ (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b
      ((Scheme.Modules.pullback (π.fiberι (IsLocalRing.closedPoint R))).obj L.sheaf)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (π.fiberι (IsLocalRing.closedPoint R)) s))) =
        (1 : Γ(T, ⊤))) : IsIso s := by
  apply Local.BaseFrameExtension.section_isIso_of_closedFiber_frame π L s
  exact normalizedTrivialSection_isIso b _ e r (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (π.fiberι (IsLocalRing.closedPoint R)) s) h

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.ClosedFiberFrames

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Families
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Closed Family Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Smoothness of actual ideal-defined families persists under the specified Cartesian ambient pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Closed.Families.FlatClosedFamily.pullbackAlong_smooth
    {S T : Scheme.{u}} {P : Over S} {Q : Over T}
    (F : Closed.Families.FlatClosedFamily P) [Smooth F.scheme.hom]
    (p : Q.left ⟶ P.left) (f : T ⟶ S) (h : IsPullback p Q.hom P.hom f) :
    Smooth (F.pullbackAlong p f h).scheme.hom :=
  MorphismProperty.of_isPullback (P := @Smooth) (ClosedFamily.Transport.closedFamilyTransport_isPullback p f h F.ideal)
    (inferInstanceAs (Smooth F.scheme.hom))

theorem Closed.Families.FlatClosedFamily.affineProjectivePullback_smooth
    {T : Scheme.{u}} {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver T n)) [Smooth F.scheme.hom]
    {R : CommRingCat.{u}} (x : Spec R ⟶ T) : Smooth (F.affineProjectivePullback x).scheme.hom :=
  F.pullbackAlong_smooth (AffineProjective.Charts.affineProjectiveChartMap x n) x (AffineProjective.Charts.affineProjectiveChartMap_isPullback x n)

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.affineFamily_smooth
    {T : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ} (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P)
    [Smooth F.family.scheme.hom] {R : CommRingCat.{u}} (x : Spec R ⟶ T) :
    Smooth (F.affineFamily x).val.scheme.hom := F.family.affineProjectivePullback_smooth x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

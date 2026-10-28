import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TrivialBundle

/-! # Residue Nonvanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ResidueNonvanishing

noncomputable section

/-! A section of a line bundle frames at a point precisely when its
actual pullback to that point's residue-field scheme is nonzero. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
universe u

theorem mem_sectionNonvanishing_iff_residue_pullback_ne_zero
    {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) (x : X) :
    x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ↔ AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (X.fromSpecResidueField x) s ≠ 0 := by
  let g := X.fromSpecResidueField x
  let y : Spec (X.residueField x) := default
  have hy : g y = x := X.fromSpecResidueField_apply x y
  have hmem : y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s) ↔ x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
    rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange g L]
    change g y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ↔ _
    rw [hy]
  constructor
  · intro hx hz
    have hh := hmem.mpr hx
    rw [hz, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.sectionNonvanishing_zero (L := L.pullback g)] at hh
    exact hh
  · intro hn
    let Z : Over (Spec (X.residueField x)) := Over.mk (𝟙 _)
    have : IsProper Z.hom := inferInstanceAs (IsProper (𝟙 (Spec (X.residueField x))))
    have : ConnectedSpace Z.left := inferInstanceAs (ConnectedSpace (Spec (X.residueField x)))
    have : IsReduced Z.left := inferInstanceAs (IsReduced (Spec (X.residueField x)))
    have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s) := Quotients.FiniteDescent.TrivialBundle.Construction.TrivialBundleFrame.isIso Z
      (L.pullback g).trivialization_of_subsingleton (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s) hn
    apply hmem.mp
    rw [AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso]
    trivial

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ResidueNonvanishing

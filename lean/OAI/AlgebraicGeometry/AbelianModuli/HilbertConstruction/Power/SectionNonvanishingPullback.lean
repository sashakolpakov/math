import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

/-! # Section Nonvanishing Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionNonvanishingPullback

noncomputable section

/-! A section of a line-bundle power pulls back to the corresponding power with the exact inverse-image nonvanishing open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y) (n : ℕ)

def pullbackPowerSection (s : Line.Bundles.structureModule Y ⟶ (L.tensorPower n).sheaf) :
    Line.Bundles.structureModule X ⟶ ((L.pullback f).tensorPower n).sheaf :=
  Ample.LineBundles.pullbackSection f s ≫ (Line.Bundles.LineBundle.powerBaseChangeIso f L n).hom

theorem pullbackPowerSection_nonvanishing (s : Line.Bundles.structureModule Y ⟶ (L.tensorPower n).sheaf) :
    Ample.LineBundles.sectionNonvanishing (pullbackPowerSection f L n s) = f ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s :=
  (Ample.Powers.sectionNonvanishing_comp_iso _ (Line.Bundles.LineBundle.powerBaseChangeIso f L n)).trans
    (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange f (L.tensorPower n) s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionNonvanishingPullback

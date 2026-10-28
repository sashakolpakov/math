import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GlobalExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Naturality

/-! # Section Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Compare power-section ratios with the original nonvanishing chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} {M : X.Modules}

/-- The canonical ratio can be read on any equal open subset. -/
theorem Power.SectionRatios.sectionRatio_on_equal_open (s t : Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : Ample.LineBundles.sectionNonvanishing s = U) [IsIso (Ample.LineBundles.pullbackSection U.ι s)] :
    (X.isoOfEq hU).inv.appTop (Section.Frames.sectionRatio s t) =
      Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι s) (Ample.LineBundles.pullbackSection U.ι t) :=
  (Frame.PullbackCoherence.sectionRatio_restrict s t (X.isoOfEq hU).inv).trans
    (Frame.PullbackCoherence.frameCoordinate_pullbackCongr (X.isoOfEq_inv_ι hU) s t)

/-- A global power numerator has its prescribed ratio under the canonical
identification of the positive-power nonvanishing open with the original one. -/
theorem Global.SectionExtension.PowerExtends.sectionRatio {L : Line.Bundles.LineBundle X}
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (n : ℕ) (hn : 0 < n) (a : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)
    (ha : Global.SectionExtension.PowerExtends s r n a) :
    (X.isoOfEq (Section.PowerLocus.sectionNonvanishing_tensorPowerSection s n hn)).inv.appTop
      (Section.Frames.sectionRatio (TensorPower.Maps.tensorPowerSection s n) a) = r := by
  have : IsIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s n)) :=
    Power.Nonvanishing.tensorPowerSection_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι s n
  exact (Power.SectionRatios.sectionRatio_on_equal_open (TensorPower.Maps.tensorPowerSection s n) a (Ample.LineBundles.sectionNonvanishing s)
    (Section.PowerLocus.sectionNonvanishing_tensorPowerSection s n hn)).trans ha

/-- Identifications of equal source opens preserve their structural coefficient maps. -/
theorem Power.SectionRatios.equal_open_appTop_coefficients (f : X ⟶ S) {U V : X.Opens} (h : U = V) :
    (X.isoOfEq h).inv.appTop.hom.comp (U.ι ≫ f).appTop.hom = (V.ι ≫ f).appTop.hom := by
  have he : (X.isoOfEq h).inv ≫ (U.ι ≫ f) = V.ι ≫ f :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ f) (X.isoOfEq_inv_ι h))
  have ha := congrArg (fun a => a.appTop.hom) he
  exact (congrArg CommRingCat.Hom.hom (Scheme.Hom.comp_appTop (X.isoOfEq h).inv (U.ι ≫ f))).symm.trans ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

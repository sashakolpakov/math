import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothBaseCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DimensionEtaleRingMaps
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Equal Dimension Etale Schemes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualDimensionEtaleSchemes

noncomputable section

/-! An unramified map between schemes smooth of the same relative dimension over a common base is etale. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem etale_of_smooth_equal_dimension {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    (d : ℕ) [SmoothOfRelativeDimension d q] [SmoothOfRelativeDimension d (f ≫ q)]
    [FormallyUnramified f] : Etale f := by
  apply (Etale.iff_smoothOfRelativeDimension_zero f).mpr
  constructor
  intro x
  obtain ⟨U, V, W, hx, eq, ef, hq, hp⟩ := Common.SmoothBaseCharts.exists_common_standardSmooth_charts f q d x
  have hc : (f.appLE V.1 W.1 ef).hom.comp (q.appLE U.1 V.1 eq).hom =
      ((f ≫ q).appLE U.1 W.1 (ef.trans (f.preimage_mono eq))).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f q U.1 V.1 W.1 eq ef)
  have h := DimensionEtaleRingMaps.ringHom_etale_of_standardSmooth_equal_dimension
    (q.appLE U.1 V.1 eq).hom (f.appLE V.1 W.1 ef).hom d hq
    ((congrArg (RingHom.IsStandardSmoothOfRelativeDimension d) hc).mpr hp)
    (f.formallyUnramified_appLE V.2 W.2 ef)
  exact ⟨V.1, V.2, W.1, W.2, hx, ef,
    RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp h⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualDimensionEtaleSchemes

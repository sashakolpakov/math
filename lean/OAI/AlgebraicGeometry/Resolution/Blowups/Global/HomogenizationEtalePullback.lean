import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback

/-! # Homogenization Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationEtalePullback.Construction

noncomputable section

/-! Native global homogenization commutes with actual étale pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothHomogenizedIdealSheaf_comap_etale {X Y : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    (q : Y ⟶ X) [Etale q] :
    (Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap q =
      Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n := by
  simp only [Homogenization.Construction.smoothHomogenizedIdealSheaf, Affine.KernelSums.Construction.idealSheaf_comap_iSup,
    IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationEtalePullback.Construction

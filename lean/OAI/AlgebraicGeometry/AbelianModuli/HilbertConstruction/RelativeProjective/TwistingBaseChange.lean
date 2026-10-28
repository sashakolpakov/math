import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.CoefficientChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseMaps

/-! # Twisting Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBaseChange

noncomputable section

/-! The relative projective twisting bundle commutes with every scheme base change through the actual relative projective base map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def relativeProjectiveTwistingBundle_baseChangeIso
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    ((TwistingBundle.relativeProjectiveTwistingBundle S n).pullback (BaseMaps.relativeProjectiveBaseMap f n)).sheaf ≅
      (TwistingBundle.relativeProjectiveTwistingBundle T n).sheaf := by
  let L := Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) n
  exact (Scheme.Modules.pullbackComp (BaseMaps.relativeProjectiveBaseMap f n)
      (BaseMaps.relativeProjectiveCoefficientProjection S n)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (BaseMaps.relativeProjectiveBaseMap_fst f n)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp (BaseMaps.relativeProjectiveCoefficientProjection T n)
      (Projective.CoefficientFunctoriality.polynomialProjectiveMap f.appTop n)).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback (BaseMaps.relativeProjectiveCoefficientProjection T n)).mapIso
      (ProjectiveTwisting.CoefficientChange.affineProjectiveTwistingBundle_coefficientIso f.appTop n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBaseChange

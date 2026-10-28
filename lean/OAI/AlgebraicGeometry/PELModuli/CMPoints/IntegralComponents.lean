import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RankSpecialization

/-! # Integral Components -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The supplied integral components are connected over the arithmetic
base. Consequently the rank of a finite locally free block on one such
component is determined at any one of its characteristic-zero points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

theorem Models.RankThreePELModel.arithmeticBase_connected : ConnectedSpace M.arithmetic.base := by
  let : IsDomain M.arithmetic.R :=
    Function.Injective.isDomain M.arithmetic.toField M.arithmetic.toField_injective
  infer_instance

theorem Models.RankThreePELModel.integralComponent_connected (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a)) :
    ConnectedSpace ((M.components a).S t).left := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcomp⟩ := hM.2.2 a
  let : ConnectedSpace M.arithmetic.base := M.arithmeticBase_connected
  let : Smooth ((M.components a).S t).hom := (hcomp t).1
  let : GeometricallyConnected ((M.components a).S t).hom := (hcomp t).2.2.2
  exact GeometricallyConnected.connectedSpace ((M.components a).S t).hom
    ((M.components a).S t).hom.isOpenMap

theorem Models.RankThreePELModel.rank_constant_on_integral_component (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a))
    {G : Scheme} (f : G ⟶ ((M.components a).S t).left)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (x y : ((M.components a).S t).left) : f.finrank x = f.finrank y := by
  let : ConnectedSpace ((M.components a).S t).left := M.integralComponent_connected hM a t
  exact f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace x y

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints

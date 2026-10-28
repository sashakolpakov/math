import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionFunctor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseActionSeparation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverOpenCoverGluing

/-! # Action Separation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionSeparation

noncomputable section

/-! Actual PEL-action values are separated on every source open cover,
without noetherian hypotheses on the test scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem relativePELAction_cover_separated (T : Over M.left) (C : T.left.OpenCover.{0}) :
    Function.Injective (fun v : (ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op T) =>
      fun i => (ActionFunctor.relativePELActionFunctor P iotaO M A).map (OverOpenCoverGluing.OverOpenCover.inclusion T C i).op v) := by
  intro v w h
  apply Subtype.ext
  have (i : C.I₀) : IsOpenImmersion (OverOpenCoverGluing.OverOpenCover.inclusion T C i).left :=
    inferInstanceAs (IsOpenImmersion (C.f i))
  apply Open.BaseActionSeparation.OpenBaseFamilies.integralAction_ext_of_open_restrictions
    (OverOpenCoverGluing.OverOpenCover.obj T C) T (OverOpenCoverGluing.OverOpenCover.inclusion T C) (fun t => C.exists_eq t) A.abelian
  intro i
  exact congrArg Subtype.val (congrFun h i)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionSeparation

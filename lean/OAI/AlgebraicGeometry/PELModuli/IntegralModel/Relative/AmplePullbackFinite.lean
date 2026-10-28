import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PullbackTransport
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperAmple

/-! # Ample Pullback Finite -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AmplePullbackFinite

noncomputable section

/-! For the actual relative map, an ample pulled-back target line
bundle forces finiteness. Pullback compatibility is by a sheaf isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B T : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B) [IsProper f]

theorem relativeMorphismBaseChange_isFinite_of_ample_pullback
    (H : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (eL : (H.pullback f).sheaf ≅ L.sheaf)
    (g : T ⟶ B) (hL : (L.pullback (pullback.fst (f ≫ q) g)).IsAmple) :
    IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) := by
  let e := HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g
  let a := pullback.fst (f ≫ q) g
  let b := pullback.fst q g
  have he : e ≫ b = a ≫ f := by
    simp only [e, a, b, HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange, pullback.map, pullback.lift_fst]
  have : IsProper e := by
    dsimp only [e]
    rw [HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange_eq]
    infer_instance
  let i : ((H.pullback b).pullback e).sheaf ≅ (L.pullback a).sheaf :=
    (Scheme.Modules.pullbackComp e b).app H.sheaf ≪≫
      (Scheme.Modules.pullbackCongr he).app H.sheaf ≪≫
      (Scheme.Modules.pullbackComp a f).symm.app H.sheaf ≪≫
      (Scheme.Modules.pullback a).mapIso eL
  exact Quotients.FiniteDescent.ProperAmple.Construction.ProperAmplePullback.isFinite e (H.pullback b) (hL.of_iso i.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AmplePullbackFinite

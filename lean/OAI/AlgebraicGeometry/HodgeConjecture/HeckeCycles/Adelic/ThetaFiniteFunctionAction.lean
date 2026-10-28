import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationSmoothness
import OAI.RepresentationTheory.Theta.Adelic.Data

/-! # Theta Finite Function Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaFiniteFunctionAction.CM

noncomputable section

/-! The actual finite function representation for whichever normalized
splitting the full AdelicTheta conclusion supplies. Its smoothness follows from
that conclusion by the proved evaluation quotient. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.Data

variable (F : Type) [Field F] [NumberField F] (a : F) (m : ℕ)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (ha : a ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F a 3 m) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F a 3 m H K)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F a 3 m H K ha C P)

def action : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H →*
    (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F (3 * m) ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F (3 * m)) :=
  Finite.FunctionAction.CM.functionAction F (3 * m)
    (fun v => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v))
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction F H K ha C P D) (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction_unramified F H K ha C P D)

theorem intertwines (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    action F a m H K ha C P D g (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m) f) =
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m) (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction F H K ha C P D g f) :=
  Finite.FunctionAction.CM.intertwines F (3 * m) _ _ _ g f

theorem smooth (hD : RepresentationTheory.Theta.Adelic.Data.FiniteConclusion F a 3 m H K ha C P D) (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F (3 * m)) :
    IsOpen {g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H | action F a m H K ha C P D g φ = φ} :=
  SurjectiveRepresentationSmoothness.CM.smooth (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m))
    (Finite.TensorRepresentatives.CM.sectionMap F (3 * m)) (Finite.FunctionAction.CM.section_identity F (3 * m))
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction F H K ha C P D) _ hD.1 φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaFiniteFunctionAction.CM

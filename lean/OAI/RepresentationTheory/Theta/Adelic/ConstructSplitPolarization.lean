import OAI.RepresentationTheory.Theta.Adelic.SplitCoordinates
import OAI.RepresentationTheory.Theta.Adelic.SplitTensor
import OAI.RepresentationTheory.Theta.Adelic.FrameChange

/-! # Construct Split Polarization -/

namespace OAI.RepresentationTheory.Theta.Adelic.ConstructSplitPolarization

noncomputable section

/-! Construction of the split-place coordinate data from a square root of
the quadratic parameter. The SL₃ identification and symplectic change of
polarization are both explicit constructions. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.SplitCoordinates OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
open OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special OAI.RepresentationTheory.Theta.Adelic.SplitTensor.Frame
open OAI.RepresentationTheory.Theta.Adelic.SplitTensor.Action OAI.RepresentationTheory.Theta.Adelic.FrameChange

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
    (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (v : FiniteSchwartz.FinitePlace F)

def constructedSplitPolarization
    (r : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (hr : r ^ 2 = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d) :
    SplitCoordinates.SplitPolarization F d H K P v := by
  let : CharZero (v.adicCompletion F) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
  have hr0 : r ≠ 0 := by
    intro h0
    apply hd
    apply (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)).injective
    rw [map_zero, ← hr, h0, zero_pow (by decide : 2 ≠ 0)]
  let HL := Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H (.inr v)
  let KL := Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K (.inr v)
  let j := Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inr v)
  have hjstar (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) : j (star z) = star (j z) :=
    Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)) d z
  have hHL : HL.val.conjTranspose = HL.val :=
    (Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose j hjstar H.val).symm.trans (congrArg (fun A => A.map j) hH)
  have hKL : KL.val.conjTranspose = -KL.val :=
    (Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose j hjstar K.val).symm.trans
      ((congrArg (fun A => A.map j) hK).trans (map_neg j.mapMatrix K.val))
  let e := SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 HL hHL
  let c := SplitTensor.Frame.splitFrame r hr hr0 HL KL hHL hKL
  refine ⟨r, hr, e.symm, FrameChange.frameChange (P.localFrame (.inr v)) c, ?_⟩
  intro g
  have hp : SplitUnitary.plusUnitary r hr hr0 HL (SpecialUnitary.includeUnitary HL.val (e.symm g)) =
      Matrix.SpecialLinearGroup.toGL g := by
    apply Units.ext
    exact congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) => A.val)
      (e.apply_symm_apply g)
  change FrameChange.frameChange (P.localFrame (.inr v)) c *
      Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic HL.val KL.val (P.localFrame (.inr v))
        (SpecialUnitary.includeUnitary HL.val (e.symm g), 1) * (FrameChange.frameChange (P.localFrame (.inr v)) c)⁻¹ = _
  rw [FrameChange.frameChange_conjugates]
  exact (SplitTensor.Action.splitFrame_action r hr hr0 HL KL hHL hKL _).trans (congrArg Weil.Local.Generators.Construction.leviSymplectic hp)

end

end OAI.RepresentationTheory.Theta.Adelic.ConstructSplitPolarization

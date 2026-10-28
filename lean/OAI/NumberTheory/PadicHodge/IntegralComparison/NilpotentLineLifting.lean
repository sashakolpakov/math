import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFrameReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.LineAffineFrames

/-! # Nilpotent Line Lifting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentLineLifting

noncomputable section

/-! A positive p-power of every actual line bundle on the closed
reduction modulo p lifts to the original p-nilpotent separated scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (p : ℕ) [Fact p.Prime] (n : ℕ)
  {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] [Surjective f] [X.IsSeparated]
  (hn : ∀ U : X.Opens, (p : Γ(X, U)) ^ (n + 1) = 0)
  (hker : ∀ (U : X.Opens) (_hU : IsAffineOpen U),
    RingHom.ker (f.app U).hom = Ideal.span {(p : Γ(X, U))})
  (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)

def lift : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X :=
  NilpotentFrameTransitions.lineBundle p n f hn hker
    (Closed.LineAffineFrames.opens f L) (Closed.LineAffineFrames.affine f L)
    (Closed.LineAffineFrames.naturalFrames f L).transitions
    (Closed.LineAffineFrames.covers f L)

def reductionIso : ((lift p n f hn hker L).pullback f).sheaf ≅
    (L.tensorPower (p ^ n)).sheaf :=
  NilpotentFrameReduction.Transitions.lineBundle_pullbackIso p n f hn hker
    (Closed.LineAffineFrames.opens f L) (Closed.LineAffineFrames.affine f L)
    (Closed.LineAffineFrames.naturalFrames f L).transitions
    (Closed.LineAffineFrames.covers f L) ≪≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor Y (p ^ n)).mapIso (Closed.LineAffineFrames.sourceIso f L)

include hn hker in
theorem exists_positive_power_lift :
    ∃ (d : ℕ), 0 < d ∧ ∃ M : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X, Nonempty ((M.pullback f).sheaf ≅ (L.tensorPower d).sheaf) :=
  ⟨p ^ n, Nat.pow_pos (Fact.out : p.Prime).pos,
    lift p n f hn hker L, ⟨reductionIso p n f hn hker L⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentLineLifting

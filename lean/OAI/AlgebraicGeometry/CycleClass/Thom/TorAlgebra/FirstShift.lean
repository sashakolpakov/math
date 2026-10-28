import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExactSequence

/-! # First Shift -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FirstShift

noncomputable section

/-! Positive-degree dimension shifting for native Tor in its first
variable, through an actual short exact sequence with projective middle term. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Tor

universe u

variable (R : Type u) [CommRing R] (N : ModuleCat.{u} R)
  (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) [Projective S.X₂]

def shiftIso (n : ℕ) : (((Tor (ModuleCat R) (n + 2)).obj S.X₃).obj N) ≅
    (((Tor (ModuleCat R) (n + 1)).obj S.X₁).obj N) := by
  let : Module.Projective R S.X₂ := ModuleCat.projective_of_module_projective _
  let : Module.Flat R S.X₂ := inferInstance
  have hz₁ := TorAlgebra.Flat.Tor.higherTor_isZero R S.X₂ N (n + 1)
  have hz₂ := TorAlgebra.Flat.Tor.higherTor_isZero R S.X₂ N n
  let : Mono (ExactSequence.Tor.connecting R N S hS (n + 1)) :=
    (ExactSequence.Tor.exact_before_connecting R N S hS (n + 1)).mono_g
      (hz₁.eq_of_src _ _)
  let : Epi (ExactSequence.Tor.connecting R N S hS (n + 1)) :=
    (ExactSequence.Tor.exact_after_connecting R N S hS (n + 1)).epi_f
      (hz₂.eq_of_tgt _ _)
  let := isIso_of_mono_of_epi (ExactSequence.Tor.connecting R N S hS (n + 1))
  exact asIso (ExactSequence.Tor.connecting R N S hS (n + 1))

end Tor

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FirstShift

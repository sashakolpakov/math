import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.ExactSequence

/-! # First Shift -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.FirstShift

noncomputable section

/-! Positive-degree dimension shifting for native Tor in its first
variable, through an actual short exact sequence with projective middle term. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] (N : ModuleCat.{u} R)
  (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) [Projective S.X₂]

def shiftIso (n : ℕ) : (((Tor (ModuleCat R) (n + 2)).obj S.X₃).obj N) ≅
    (((Tor (ModuleCat R) (n + 1)).obj S.X₁).obj N) := by
  let : Module.Projective R S.X₂ := ModuleCat.projective_of_module_projective _
  let : Module.Flat R S.X₂ := inferInstance
  have hz₁ := ProjectionFormula.Tor.Flat.higherTor_isZero R S.X₂ N (n + 1)
  have hz₂ := ProjectionFormula.Tor.Flat.higherTor_isZero R S.X₂ N n
  let : Mono (ExactSequence.connecting R N S hS (n + 1)) :=
    (ExactSequence.exact_before_connecting R N S hS (n + 1)).mono_g
      (hz₁.eq_of_src _ _)
  let : Epi (ExactSequence.connecting R N S hS (n + 1)) :=
    (ExactSequence.exact_after_connecting R N S hS (n + 1)).epi_f
      (hz₂.eq_of_tgt _ _)
  let := isIso_of_mono_of_epi (ExactSequence.connecting R N S hS (n + 1))
  exact asIso (ExactSequence.connecting R N S hS (n + 1))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.FirstShift

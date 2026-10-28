import OAI.Geometry.ComplexBall.ArithmeticQuotient
import OAI.NumberTheory.Approximation.Weak
import OAI.NumberTheory.ArithmeticGroups.Lattices.ArithmeticLatticeCompactness
import OAI.NumberTheory.ArithmeticGroups.TorsionFreeLevel

/-! # Arithmetic Quotient Free -/

namespace OAI.Geometry.ComplexBall.ArithmeticQuotientFree

noncomputable section

/-! Discharge the three full external results used by ArithmeticQuotient. The Lattices input
is the same polynomial-group/arithmetic-presentation interface for which
the ArithmeticQuotient helper files construct and prove all unitary realizations. The
universe-zero Lattices theorem is applied through `Universe` to the image
field in C; the original CM field remains universe polymorphic. -/

theorem weakApproximationInput_proved (E : Type*) [Field E] [NumberField E] :
    Fields.ArithmeticQuotient.WeakApproximationInput E := by
  intro ι _ v hn hd
  exact NumberTheory.Approximation.Weak.HodgeWeakApproximation.weak_approximation E v hn hd

theorem arithmeticLatticeInput_proved (k : Type) [Field k] [NumberField k] :
    ArithmeticQuotient.ArithmeticLatticeInput k := by
  intro Gk GInf _ _ _ _ _ _ _ G δ Γ₀ Γ hmodel hcomm
  exact NumberTheory.ArithmeticGroups.Lattices.ArithmeticLatticeCompactness.arithmetic_lattice_and_anisotropic_compactness
    G δ Γ₀ Γ hmodel hcomm

theorem torsionFreeLevelsInput_proved (E : Type*) [Field E] [NumberField E]
    [NumberField.IsCMField E] : Levels.ArithmeticQuotient.TorsionFreeLevelsInput E := by
  intro b Λ hΛ N₀ hN₀
  exact NumberTheory.ArithmeticGroups.TorsionFreeLevel.sufficiently_deep_principal_levels_torsion_free b Λ hΛ N₀ hN₀

end

end OAI.Geometry.ComplexBall.ArithmeticQuotientFree

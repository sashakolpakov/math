import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalWeightIntegration

/-! # Anisotropic Integer Weights -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicIntegerWeights.Construction

noncomputable section

/-! The exact cocharacter definition of anisotropy rules out every
nonzero integer diagonal element of the infinitesimal matrix group. -/

open scoped Classical
open _root_.Matrix

theorem charZero_two_zpow_eq_one_iff
    {k : Type} [Field k] [CharZero k] (z : ℤ) : (2 : k) ^ z = 1 ↔ z = 0 := by
  constructor
  · intro hz
    have hrat : (2 : ℚ) ^ z = 1 := by
      apply (Rat.castHom k).injective
      simpa only [map_zpow₀, map_ofNat, map_one] using hz
    exact (zpow_eq_one_iff_right₀ (by norm_num : (0 : ℚ) ≤ 2) (by norm_num : (2 : ℚ) ≠ 1)).mp hrat
  · rintro rfl
    exact zpow_zero _

theorem anisotropic_integer_diagonal_weights_zero
    {k : Type} [Field k] [CharZero k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) (w : Fin G.dimension → ℤ)
    (hw : Matrix.diagonal (fun i => (w i : k)) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) : w = 0 := by
  let c := DiagonalWeightIntegration.Construction.diagonalInfinitesimalCocharacter G.matrixGroup w hw
  let t : kˣ := Units.mk0 2 (by norm_num)
  have he := DFunLike.congr_fun (haniso c k (RingHom.id k)) t
  funext i
  have hi := congrArg (fun g : G.matrixGroup.RationalPoints => g.val i i) he
  change (Matrix.diagonal (fun j => ((t ^ w j : kˣ) : k))) i i =
    (1 : Matrix (Fin G.dimension) (Fin G.dimension) k) i i at hi
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hi
  rw [Units.val_zpow_eq_zpow_val] at hi
  exact (charZero_two_zpow_eq_one_iff (k := k) (w i)).mp hi

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicIntegerWeights.Construction

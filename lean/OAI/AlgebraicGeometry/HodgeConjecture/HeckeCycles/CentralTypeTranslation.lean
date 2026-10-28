import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives

/-! # Central Type Translation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CentralTypeTranslation.CM

noncomputable section

/-! Central convolution translates every exponent of the actual raw
cocharacter basis, with its inverse-representative convention retained. -/

open scoped Classical
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction

variable {s : ℕ}

def shifted (t : AbelianScheme.TateComparison.Local.LocalType s) (a : Fin s → ℤ) (h : ℤ) (n : ℕ) : AbelianScheme.TateComparison.Local.LocalType s where
  multiplier := h * n + t.multiplier
  exponent v i := a v * n + t.exponent v i
  dominant v _ _ hij := add_le_add (le_refl _) (t.dominant v hij)

theorem representative_shifted (q : ℕ) [Fact q.Prime]
    (t : AbelianScheme.TateComparison.Local.LocalType s) (a : Fin s → ℤ) (h : ℤ) (n : ℕ) :
    AbelianScheme.TateComparison.HeckeKernel.representative s q (shifted t a h n) =
      AbelianScheme.CentralAction.CentralRepresentatives.Construction.centralRepresentative s q a h ^ n * AbelianScheme.TateComparison.HeckeKernel.representative s q t := by
  apply Prod.ext
  · funext v
    change AbelianScheme.TateComparison.CentralConvolution.diagonalHom (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (a v * (n : ℤ) + t.exponent v i)) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a v) ^ n *
        AbelianScheme.TateComparison.CentralConvolution.diagonalHom (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ t.exponent v i)
    have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) (AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a v) =
        AbelianScheme.TateComparison.CentralConvolution.diagonalHom (fun _ => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a v) := Units.ext rfl
    rw [hs, ← map_pow, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, Pi.pow_apply, zpow_add, zpow_mul, zpow_natCast]
  · change AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (h * (n : ℤ) + t.multiplier) =
      (AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ h) ^ n * AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ t.multiplier
    rw [zpow_add, zpow_mul, zpow_natCast]

theorem basis_translation (q : ℕ) [Fact q.Prime]
    (basis : AbelianScheme.TateComparison.Local.LocalType s → AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
    (hb : ∀ t, AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t))
    (t : AbelianScheme.TateComparison.Local.LocalType s) (a : Fin s → ℤ) (h : ℤ) (n : ℕ) :
    AbelianScheme.CentralAction.CentralRepresentatives.Construction.centralCoset s q a h ^ n * basis t = basis (shifted t a h n) := by
  apply AbelianScheme.TateComparison.HeckeKernel.rawDoubleCoset_unique (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (g := AbelianScheme.TateComparison.HeckeKernel.representative s q (shifted t a h n))
  · rw [representative_shifted]
    exact AbelianScheme.TateComparison.CentralConvolution.central_pow_mul_isRaw _ _ _ (hb t) n
  · exact hb _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CentralTypeTranslation.CM

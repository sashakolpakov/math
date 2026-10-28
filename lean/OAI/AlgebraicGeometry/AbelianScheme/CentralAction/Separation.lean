import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Hecke
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan

/-! # Separation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Separation.Construction

noncomputable section

/-! A dominant representative in a central coset has exactly the central
exponents. Integral matrix bounds prove this without an extra Cartan input. -/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan

variable (s q : ℕ) [Fact q.Prime]

theorem scalar_inverse_diagonal_int (a : ℤ) (b : Fin 3 → ℤ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (TateComparison.HeckeKernel.qUnit q ^ a) *
      (TateComparison.HeckeKernel.diagonalUnit (fun i => TateComparison.HeckeKernel.qUnit q ^ b i))⁻¹ =
        TateComparison.HeckeKernel.diagonalUnit (fun i => TateComparison.HeckeKernel.qUnit q ^ (a - b i)) := by
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) (TateComparison.HeckeKernel.qUnit q ^ a) =
      TateComparison.CentralConvolution.diagonalHom (fun _ => TateComparison.HeckeKernel.qUnit q ^ a) := by
    apply Units.ext
    rfl
  rw [hs]
  change TateComparison.CentralConvolution.diagonalHom _ * (TateComparison.CentralConvolution.diagonalHom _)⁻¹ = TateComparison.CentralConvolution.diagonalHom _
  rw [← map_inv, ← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.inv_apply, ← zpow_sub]

theorem central_coset_representative_unique (t : TateComparison.Local.LocalType s)
    (a : Fin s → ℤ) (h : ℤ)
    (hcoset : (QuotientGroup.mk (TateComparison.HeckeKernel.representative s q t)⁻¹ : TateComparison.HeckeKernel.SplitGroup s q ⧸ TateComparison.HeckeKernel.integralLevel s q) =
      QuotientGroup.mk (CentralRepresentatives.Construction.centralRepresentative s q a h)⁻¹) :
    t = CentralRepresentatives.Construction.centralType a h := by
  have hm : CentralRepresentatives.Construction.centralRepresentative s q a h * (TateComparison.HeckeKernel.representative s q t)⁻¹ ∈ TateComparison.HeckeKernel.integralLevel s q := by
    have hh := QuotientGroup.eq.mp hcoset.symm
    simpa only [inv_inv] using hh
  have hn := Hecke.Construction.integralLevel_multiplier_norm_one s q _ hm
  change ‖((TateComparison.HeckeKernel.qUnit q ^ h * (TateComparison.HeckeKernel.qUnit q ^ t.multiplier)⁻¹ : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 at hn
  rw [← zpow_sub, Units.val_zpow_eq_zpow_val, norm_zpow] at hn
  have hh : h - t.multiplier = 0 :=
    (zpow_eq_one_iff_right₀ (norm_nonneg (TateComparison.HeckeKernel.qUnit q : ℚ_[q]))
      (ne_of_lt (Padic.norm_p_lt_one (p := q)))).mp hn
  have hmult : t.multiplier = h := by omega
  have hexp : t.exponent = fun v _ => a v := by
    funext v i
    have hb := (TateComparison.IntegralCartan.integralSplitBound_of_level s q hm).2 v
    change TateComparison.IntegralCartan.IntegralGLBound q 0
      (Matrix.GeneralLinearGroup.scalar (Fin 3) (TateComparison.HeckeKernel.qUnit q ^ a v) *
        (TateComparison.HeckeKernel.diagonalUnit (fun i => TateComparison.HeckeKernel.qUnit q ^ t.exponent v i))⁻¹) at hb
    rw [scalar_inverse_diagonal_int] at hb
    have hi := (TateComparison.IntegralCartan.integralGLBound_diagonal_iff q 0 _).mp hb i
    omega
  cases t
  dsimp only at hmult hexp
  cases hmult
  cases hexp
  rfl

theorem central_orbit_representative_unique (t : TateComparison.Local.LocalType s)
    (a : Fin s → ℤ) (h : ℤ)
    (horbit : (QuotientGroup.mk (TateComparison.HeckeKernel.representative s q t)⁻¹ : TateComparison.HeckeKernel.SplitGroup s q ⧸ TateComparison.HeckeKernel.integralLevel s q) ∈
      TateComparison.HeckeKernel.doubleCosetOrbit (TateComparison.HeckeKernel.integralLevel s q) (CentralRepresentatives.Construction.centralRepresentative s q a h)) :
    t = CentralRepresentatives.Construction.centralType a h := by
  rw [TateComparison.CentralConvolution.doubleCosetOrbit_central _ _ (CentralRepresentatives.Construction.centralRepresentative_commutes s q a h)] at horbit
  exact central_coset_representative_unique s q t a h (Set.mem_singleton_iff.mp horbit)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Separation.Construction

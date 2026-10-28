import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

/-! # Neighbor Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NeighborOperators

noncomputable section

/-! The original integral ordinary-neighbor operators are exactly the
central powers times the native minuscule operators, with raw coefficients. -/

open scoped Classical
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM

theorem native_neighbor_representative {s q : ℕ} [Fact q.Prime]
    (active : Fin s) (side : Fin s → Bool) (i : Fin 3) :
    AbelianScheme.TateComparison.HeckeKernel.representative s q (HeckeCycles.Neighbor.Types.CM.integralType active side i).val =
      AbelianScheme.CentralAction.CentralRepresentatives.Construction.centralRepresentative s q (AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents active side) 1 ^ (i.val + 1) *
        AbelianScheme.TateComparison.HeckeKernel.representative s q (MinusculeParameters.activeMinusculeType active ⟨i.val + 1, by omega⟩) := by
  apply Prod.ext
  · funext v
    change AbelianScheme.TateComparison.CentralConvolution.diagonalHom (fun k => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ ((Isogenies.NeighborCounting.HeckeExponents.neighborExponents active side i v k : ℕ) : ℤ)) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents active side v) ^
        (i.val + 1) * AbelianScheme.TateComparison.CentralConvolution.diagonalHom
          (fun k => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (if v = active ∧ k.val < i.val + 1 then (1 : ℤ) else 0))
    have he : Matrix.GeneralLinearGroup.scalar (Fin 3) (AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents active side v) =
        AbelianScheme.TateComparison.CentralConvolution.diagonalHom (fun _ => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents active side v) := by
      apply Units.ext
      rfl
    rw [he, ← map_pow, ← map_mul]
    congr 1
    funext k
    by_cases hv : v = active
    · simp [Isogenies.NeighborCounting.HeckeExponents.neighborExponents, Isogenies.NeighborCounting.HeckeExponents.activeExponents, Isogenies.NeighborCounting.HeckeExponents.neighborLevel, AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents, hv]
    · cases hs : side v with
      | false => simp [Isogenies.NeighborCounting.HeckeExponents.neighborExponents, AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents, hv, hs]
      | true =>
        simp [Isogenies.NeighborCounting.HeckeExponents.neighborExponents, Isogenies.NeighborCounting.HeckeExponents.neighborLevel, AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents, hv, hs]
        norm_cast
  · change AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ ((Isogenies.NeighborCounting.HeckeExponents.neighborLevel i : ℕ) : ℤ) =
      (AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (1 : ℤ)) ^ (i.val + 1) * AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (0 : ℤ)
    rw [zpow_one, zpow_zero, mul_one, ← zpow_natCast]
    rfl

theorem native_neighbor_raw_basis {s q : ℕ} [Fact q.Prime]
    (basis : AbelianScheme.TateComparison.Local.LocalType s → AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
    (hbasis : ∀ t, AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t))
    (active : Fin s) (side : Fin s → Bool) (i : Fin 3) :
    AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q active side ^ (i.val + 1) *
        basis (MinusculeParameters.activeMinusculeType active ⟨i.val + 1, by omega⟩) =
      basis (HeckeCycles.Neighbor.Types.CM.integralType active side i).val := by
  apply AbelianScheme.TateComparison.HeckeKernel.rawDoubleCoset_unique (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q)
    (g := AbelianScheme.TateComparison.HeckeKernel.representative s q (HeckeCycles.Neighbor.Types.CM.integralType active side i).val)
  · rw [native_neighbor_representative]
    exact AbelianScheme.TateComparison.CentralConvolution.central_pow_mul_isRaw (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q)
      (AbelianScheme.CentralAction.CentralRepresentatives.Construction.centralRepresentative s q (AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents active side) 1)
      (AbelianScheme.CentralAction.CentralRepresentatives.Construction.centralRepresentative_commutes s q (AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents active side) 1)
      (hbasis _) (i.val + 1)
  · exact hbasis _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NeighborOperators

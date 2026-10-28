import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices

/-! # Relative Position Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionChoices

noncomputable section

/-! Raw rank-three double-coset supports classify relative-position
lattice choices above every full source lattice. The source basis is
constructed from ElementaryDivisors and removed by the lattice equivalence. -/

variable (q : ℕ) [Fact q.Prime]

def standardRankThreeLattice : Duality.RankThreeLattice ℤ_[q] ℚ_[q] :=
  ⟨IsogenyQuotient.BlockHeckeChoices.Construction.standardBlockLattice q, inferInstance⟩

def standardRawRelativePositionEquiv (a : Fin 3 → ℕ) :
    IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
      (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a i : ℤ))) ≃
    {M : Duality.RankThreeLattice ℤ_[q] ℚ_[q] //
      Duality.RelativePosition (q : ℤ_[q]) (fun i => (a i : ℤ)) (standardRankThreeLattice q) M} :=
  IsogenyQuotient.BlockHeckeChoices.Construction.rawBlockSmithChoicesEquiv q a

def rawRelativePositionEquiv (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (L : Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (a : Fin 3 → ℕ) :
    IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
      (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a i : ℤ))) ≃
    {M : Duality.RankThreeLattice ℤ_[q] ℚ_[q] // Duality.RelativePosition (q : ℤ_[q]) (fun i => (a i : ℤ)) L M} := by
  have hbase := Duality.rankThreeLattice_basis hElementaryDivisors (q : ℤ_[q]) PadicInt.irreducible_p L
  let b := hbase.choose
  have hb : L.val = Submodule.span ℤ_[q] (Set.range b) := hbase.choose_spec
  let e := (Pi.basisFun ℚ_[q] (Fin 3)).equiv b (Equiv.refl (Fin 3))
  have he : (Pi.basisFun ℚ_[q] (Fin 3)).map e = b := by
    ext i : 1
    exact Module.Basis.equiv_apply (Pi.basisFun ℚ_[q] (Fin 3)) i b (Equiv.refl (Fin 3))
  have hs : RelativePositionTransport.rankThreeLatticeEquiv e (standardRankThreeLattice q) = L := by
    apply Subtype.ext
    rw [RelativePositionTransport.rankThreeLatticeEquiv_val]
    change (Submodule.span ℤ_[q] (Set.range (Pi.basisFun ℚ_[q] (Fin 3)))).map
      (e.toLinearMap.restrictScalars ℤ_[q]) = L.val
    rw [RelativePositionTransport.map_basis_span, he, ← hb]
  refine (standardRawRelativePositionEquiv q a).trans
    ((RelativePositionTransport.rankThreeLatticeEquiv e).subtypeEquiv fun M => ?_)
  rw [← hs, RelativePositionTransport.relativePosition_map_iff]

theorem relativePositionChoices_card (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (L : Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (a : Fin 3 → ℕ) :
    Nat.card {M : Duality.RankThreeLattice ℤ_[q] ℚ_[q] //
      Duality.RelativePosition (q : ℤ_[q]) (fun i => (a i : ℤ)) L M} =
      Nat.card (IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
        (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a i : ℤ)))) :=
  Nat.card_congr (rawRelativePositionEquiv q hElementaryDivisors L a).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionChoices

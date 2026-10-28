import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockTateCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateChoices

/-! # Block Tate Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockTateChoices.Construction

noncomputable section

/-!
The raw rank-three Hecke support classifies typed subgroups of an actual
split finite Tate block. The comparison uses the restricted evaluation
map and an integral basis of that same source Tate block.
-/

variable (q : ℕ) [Fact q.Prime] {H I : Type*} [AddCommGroup H] (h : ℕ)
  (θ : (I → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] (TateComparison.Add.Tate.Module (H := H) q))
  (ψ : (I → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] (TateComparison.Add.Tate.torsion q H h))
  (heval : ∀ a, (TateComparison.Evaluation.Tate.evaluate q h).comp (θ a) = (ψ a).comp (TateComparison.Evaluation.Tate.evaluate q h))
  (hdiv : ∀ x : H, ∃ y, q • y = x) (i : I)
  (b : Module.Basis (Fin 3) ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i))

def standardLatticeTateBlockEquiv :
    TypedLatticeChoices.Construction.BoundedLatticeQuotient q h (BlockHeckeChoices.Construction.standardBlockLattice q) ≃+ TateComparison.ProductActionDecomposition.ProductAction.block ψ i :=
  (TateChoices.Construction.standardBoundedLatticeResidues q h).trans
    (BlockTateCoordinates.Construction.blockTateTorsionCoordinates q h θ ψ heval hdiv i b).symm

def rawTateBlockSubgroupChoicesEquiv (a : Fin 3 → ℕ)
    (ha : ∀ j, a j ≤ h) (hdominant : Antitone a) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput) :
    Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (BlockHeckeChoices.Construction.blockDiagonal q (fun j => (a j : ℤ))) ≃
      {F : AddSubgroup (TateComparison.ProductActionDecomposition.ProductAction.block ψ i) // Nonempty (F ≃+ (∀ j, ZMod (q ^ a j)))} :=
  (BlockHeckeChoices.Construction.rawBlockSubgroupChoicesEquiv q h a ha hdominant h_ElementaryDivisors).trans
    (TateChoices.Construction.typedAdditiveSubgroupEquiv (standardLatticeTateBlockEquiv q h θ ψ heval hdiv i b))

theorem standardLatticeTateBlockEquiv_evaluate (x : TateComparison.ProductActionDecomposition.ProductAction.block θ i) :
    standardLatticeTateBlockEquiv q h θ ψ heval hdiv i b
      ((TateChoices.Construction.standardBoundedLatticeResidues q h).symm (IsogenyQuotient.Basis.Construction.basisCoordinateResidues q b (fun _ => h) x)) =
        TateComparison.ProductActionDecomposition.ProductAction.blockMap θ ψ (TateComparison.Evaluation.Tate.evaluate q h) heval i x := by
  change (BlockTateCoordinates.Construction.blockTateTorsionCoordinates q h θ ψ heval hdiv i b).symm
    (TateChoices.Construction.standardBoundedLatticeResidues q h ((TateChoices.Construction.standardBoundedLatticeResidues q h).symm _)) = _
  rw [AddEquiv.apply_symm_apply, ← BlockTateCoordinates.Construction.blockTateTorsionCoordinates_apply q h θ ψ heval hdiv i b x,
    AddEquiv.symm_apply_apply]

theorem rawTateBlockSubgroupChoicesEquiv_membership (a : Fin 3 → ℕ)
    (ha : ∀ j, a j ≤ h) (hdominant : Antitone a) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput)
    (c : Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (BlockHeckeChoices.Construction.blockDiagonal q (fun j => (a j : ℤ))))
    (x : TateComparison.ProductActionDecomposition.ProductAction.block θ i) :
    TateComparison.ProductActionDecomposition.ProductAction.blockMap θ ψ (TateComparison.Evaluation.Tate.evaluate q h) heval i x ∈
        (rawTateBlockSubgroupChoicesEquiv q h θ ψ heval hdiv i b a ha hdominant h_ElementaryDivisors c).val ↔
      (TateChoices.Construction.standardBoundedLatticeResidues q h).symm (IsogenyQuotient.Basis.Construction.basisCoordinateResidues q b (fun _ => h) x) ∈
        (BlockHeckeChoices.Construction.rawBlockSubgroupChoicesEquiv q h a ha hdominant h_ElementaryDivisors c).val := by
  rw [← standardLatticeTateBlockEquiv_evaluate q h θ ψ heval hdiv i b x]
  exact TateChoices.Construction.typedAdditiveSubgroupEquiv_membership _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockTateChoices.Construction

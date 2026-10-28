import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairedBlocks
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CharacterSeparation
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Rational

/-! # Split Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Rosati balance and the actual separated local characters force the
chosen/opposite block decomposition of a nondegenerate rational form. -/

section Coordinates

variable {F V I R : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Fintype I] [DecidableEq I]

def SplitPairing.coordinateScalarMap (c : I → F) : (I → V) →ₗ[F] (I → V) :=
  LinearMap.pi (fun i => c i • LinearMap.proj i)

omit [Fintype I] in
theorem SplitPairing.coordinateScalarMap_single (c : I → F) (i : I) (x : V) :
    SplitPairing.coordinateScalarMap c (Pi.single i x : I → V) = c i • (Pi.single i x : I → V) := by
  funext j
  change c j • (Pi.single i x : I → V) j = c i • (Pi.single i x : I → V) j
  by_cases hj : j = i
  · subst j; rfl
  · simp only [Pi.single_eq_of_ne hj, smul_zero]

omit [Fintype I] in
theorem SplitPairing.balanced_blocks_orthogonal (B : LinearMap.BilinForm F (I → V))
    (τ : I → I) (hτ : Function.Involutive τ) (χ : R → I → F)
    (hχ : ∀ i j, i ≠ j → ∃ a, χ a i ≠ χ a j)
    (hbal : ∀ a x y, B (SplitPairing.coordinateScalarMap (fun i => χ a (τ i)) x) y =
      B x (SplitPairing.coordinateScalarMap (χ a) y))
    (i j : I) (hij : i ≠ τ j) (x y : V) : B (Pi.single i x) (Pi.single j y) = 0 := by
  have hne : τ i ≠ j := fun he => hij ((hτ i).symm.trans (congrArg τ he))
  obtain ⟨a, ha⟩ := hχ (τ i) j hne
  have he := hbal a (Pi.single i x) (Pi.single j y)
  rw [SplitPairing.coordinateScalarMap_single, SplitPairing.coordinateScalarMap_single,
    map_smul, LinearMap.smul_apply, map_smul] at he
  change χ a (τ i) * B (Pi.single i x) (Pi.single j y) =
    χ a j * B (Pi.single i x) (Pi.single j y) at he
  by_contra hz
  exact ha (mul_right_cancel₀ hz he)

end Coordinates

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)

def Data.SphericalPELAlbaneseData.oppositeBlock (v : Fin s × Bool) : Fin s × Bool := (v.1, !v.2)

theorem Data.SphericalPELAlbaneseData.oppositeBlock_involutive : Function.Involutive (Data.SphericalPELAlbaneseData.oppositeBlock (s := s)) := by
  intro v
  exact Prod.ext rfl (Bool.not_not v.2)

include hg in
theorem Data.SphericalPELAlbaneseData.splitPairing_block_nondegenerate (B : LinearMap.BilinForm ℚ_[q] (Rational.SplitTateSpace s q))
    (hB : B.Nondegenerate)
    (hbal : ∀ (a : NumberField.RingOfIntegers E) x y,
      B (SplitPairing.coordinateScalarMap (fun i => (D.localCharacter (Data.SphericalPELAlbaneseData.oppositeBlock i) a : ℚ_[q])) x) y =
        B x (SplitPairing.coordinateScalarMap (fun i => (D.localCharacter i a : ℚ_[q])) y))
    (v : Fin s × Bool) : (PairedBlocks.oppositeBlockPairing B Data.SphericalPELAlbaneseData.oppositeBlock v).Nondegenerate := by
  apply PairedBlocks.oppositeBlockPairing_nondegenerate B Data.SphericalPELAlbaneseData.oppositeBlock Data.SphericalPELAlbaneseData.oppositeBlock_involutive.injective hB
  exact SplitPairing.balanced_blocks_orthogonal B Data.SphericalPELAlbaneseData.oppositeBlock Data.SphericalPELAlbaneseData.oppositeBlock_involutive
    (fun a i => (D.localCharacter i a : ℚ_[q]))
    (fun i j hij => D.rationalCharacter_separates hg hij) hbal

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.StructureRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverages
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TameCharacters

/-! # Projectors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual tame character projections on the multiplication pushforward over a scheme with a coefficient-field map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {S : Scheme.{u}} {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g S) (c : K →+* Γ(A.scheme.left, ⊤)) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.fullLevelMultiplicationProjector
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) :
    End (A.multiplicationStructurePushforward N) :=
  Sheaf.CharacterAverages.sheafCharacterAverage c (A.multiplicationStructurePushforward N)
    (A.fullLevelStructureRepresentation level) χ

theorem Abelian.Schemes.AbelianScheme.fullLevelMultiplicationProjector_idempotent
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ)
    (hN : (N : K) ≠ 0) :
    A.fullLevelMultiplicationProjector c level χ ≫ A.fullLevelMultiplicationProjector c level χ =
      A.fullLevelMultiplicationProjector c level χ :=
  Sheaf.CharacterAverages.sheafCharacterAverage_idempotent c _ _ χ (TameCharacters.fullLevelCharacter_order_nonzero K g N hN)

theorem Abelian.Schemes.AbelianScheme.fullLevelMultiplicationProjector_orthogonal
    (χ ψ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ)
    (hN : (N : K) ≠ 0) (h : ψ ≠ χ) :
    A.fullLevelMultiplicationProjector c level ψ ≫ A.fullLevelMultiplicationProjector c level χ = 0 :=
  Sheaf.CharacterAverages.sheafCharacterAverage_orthogonal c _ _ χ ψ (TameCharacters.fullLevelCharacter_order_nonzero K g N hN) h

theorem Abelian.Schemes.AbelianScheme.fullLevelMultiplicationProjector_sum [IsAlgClosed K]
    [Fintype (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ)]
    (hN : (N : K) ≠ 0) :
    ∑ χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ,
      A.fullLevelMultiplicationProjector c level χ = 𝟙 (A.multiplicationStructurePushforward N) := by
  have hG := TameCharacters.fullLevelCharacter_order_nonzero K g N hN
  have := TameCharacters.tameFiniteAbelian_hasEnoughRoots K _ hG
  exact Sheaf.CharacterAverages.sheafCharacterAverage_sum c _ _ hG

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

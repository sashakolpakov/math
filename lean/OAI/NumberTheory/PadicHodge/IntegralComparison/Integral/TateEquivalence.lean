import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TatePairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.FiniteLimit

/-! # Tate Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateEquivalence

noncomputable section

/-! Actual integral H¹ of an abelian variety is the additive dual of its
actual geometric Tate module. Surjectivity uses genuine pro-étale cocycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TatePairing

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

theorem finiteCharacter_surjective (n : ℕ) : Function.Surjective (TatePairing.finiteCharacter ℓ A hℓ n) := by
  intro χ
  obtain ⟨x, hx⟩ := Finite.TorsionCharacterEquivalence.character_surjective ℓ n A hℓ
    (χ.comp (TatePairing.torsionEquiv ℓ A n).symm.toAddMonoidHom)
  refine ⟨x, ?_⟩
  apply AddMonoidHom.ext
  intro t
  change TorsionPointCharacter.character ℓ n A hℓ x (TatePairing.torsionEquiv ℓ A n t) = χ t
  rw [hx]
  exact congrArg χ ((TatePairing.torsionEquiv ℓ A n).symm_apply_apply t)

def finiteEquiv (n : ℕ) : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1 ≃+
    (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Geometric.TateModule.Points A) n →+ ZMod (ℓ ^ n)) :=
  AddEquiv.ofBijective ({
    toFun := TatePairing.finiteCharacter ℓ A hℓ n
    map_zero' := by
      apply AddMonoidHom.ext
      intro t
      change TorsionPointCharacter.character ℓ n A hℓ 0 _ = 0
      rw [map_zero]
      rfl
    map_add' x y := by
      apply AddMonoidHom.ext
      intro t
      change TorsionPointCharacter.character ℓ n A hℓ (x + y) _ = _
      rw [map_add]
      rfl } : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1 →+
        (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Geometric.TateModule.Points A) n →+ ZMod (ℓ ^ n)))
    ⟨TatePairing.finiteCharacter_injective ℓ A hℓ n, finiteCharacter_surjective ℓ A hℓ n⟩

theorem integralFamily_surjective : Function.Surjective (TatePairing.integralFamily ℓ A hℓ) := by
  intro χ
  let x (n : ℕ) := (finiteEquiv ℓ A hℓ n).symm (χ.val n)
  have hχ (n : ℕ) : TatePairing.finiteCharacter ℓ A hℓ n (x n) = χ.val n :=
    (finiteEquiv ℓ A hℓ n).apply_symm_apply (χ.val n)
  have hx (n : ℕ) : Sheaf.H.map
      (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left) 1 (x (n + 1)) = x n := by
    apply TatePairing.finiteCharacter_injective ℓ A hℓ n
    apply AddMonoidHom.ext
    intro t
    obtain ⟨s, rfl⟩ := Geometric.TateModule.evaluate_surjective A ℓ hℓ n t
    have hs : AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate ℓ n s = AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.transition ℓ n (s.val (n + 1)) := (s.property n).symm
    rw [hs, TatePairing.finiteCharacter_transition, hχ, hχ]
    exact (χ.property n (s.val (n + 1))).symm
  obtain ⟨z, hz⟩ := FiniteLimit.exists_class ℓ A hℓ x hx
  refine ⟨z, ?_⟩
  apply Subtype.ext
  funext n
  change TatePairing.finiteCharacter ℓ A hℓ n (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 z) = χ.val n
  rw [hz, hχ]

theorem pairing_surjective : Function.Surjective (TatePairing.pairing ℓ A hℓ) := by
  intro f
  obtain ⟨χ, hχ⟩ := (TateCompatibleCharacters.equiv ℓ (Geometric.TateModule.divisible A ℓ hℓ)).surjective f
  obtain ⟨x, hx⟩ := integralFamily_surjective ℓ A hℓ χ
  exact ⟨x, (congrArg (TateCompatibleCharacters.toDual ℓ) hx).trans hχ⟩

def equiv : A.left.EllAdicCohomology ℓ 1 ≃+
    Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) :=
  AddEquiv.ofBijective (TatePairing.pairing ℓ A hℓ)
    ⟨TatePairing.pairing_injective ℓ A hℓ, pairing_surjective ℓ A hℓ⟩

@[simp] theorem equiv_apply (x : A.left.EllAdicCohomology ℓ 1) :
    equiv ℓ A hℓ x = TatePairing.pairing ℓ A hℓ x := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateEquivalence

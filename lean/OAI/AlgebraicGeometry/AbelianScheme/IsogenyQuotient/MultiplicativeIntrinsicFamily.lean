import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeChoiceKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.IntrinsicFamily

/-! # Multiplicative Intrinsic Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeIntrinsicFamily.Construction

noncomputable section

/-!
The universal native quotient construction applies to the actual
G_m-valued torsion pairings. Their root-of-unity factorization supplies
the etale target, and the universal family keeps the prescribed full kernel.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))}

theorem universalNativeFamily_roots_iff
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (n : ℕ)
    (M : Fin s → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (p r : Fin s → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
    (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X)) :
    Universal.IntrinsicFamily.Construction.UniversalNativeFamily A n M p r (MultiplicativeChoiceKernel.Construction.blockPairingsToRoots n s p r e) ↔
      Universal.IntrinsicFamily.Construction.UniversalNativeFamily A n M p r e := by
  unfold Universal.IntrinsicFamily.Construction.UniversalNativeFamily
  apply exists_congr
  intro Q
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply exists_congr
  intro repr
  rw [MultiplicativeChoiceKernel.Construction.choiceFullKernel_roots_target n s p r e M (Universal.Choices.Construction.universalBlockChoice n s M p repr)]

theorem universal_multiplicative_native_family_from_TorsionQuotient_FiniteDescent
    [CharZero K] (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (n : ℕ) (hn : 0 < n)
    (hcop : Nat.Coprime n N)
    (M : Fin s → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (p r : Fin s → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
    (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X))
    (hsep : ∀ i j : ChoiceKernel.Construction.KernelIndex s, i ≠ j →
      Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p r j) ≫
        Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p r i) = 1)
    (scalar : NumberField.RingOfIntegers E → ChoiceKernel.Construction.KernelIndex s → ℤ)
    (hscalar : ∀ a i, OppositeKernel.Construction.torsionBlockInclusion n (ChoiceKernel.Construction.choiceKernelProjector s p r i) ≫ A.action.map a =
      (OppositeKernel.Construction.torsionBlockInclusion n (ChoiceKernel.Construction.choiceKernelProjector s p r i)) ^ scalar a i)
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{0}) (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) :
    Universal.IntrinsicFamily.Construction.UniversalNativeFamily A n M p r e := by
  let : Etale (Multiplicative.Construction.rootsOfUnityScheme T.left n).hom := Multiplicative.Construction.rootsOfUnityScheme_etale T.left n
    (Unit.Construction.positive_integer_unit_on_characteristic_zero_base T.hom n hn)
  let : IsSeparated (Multiplicative.Construction.rootsOfUnityScheme T.left n).hom := Multiplicative.Construction.rootsOfUnityScheme_separated T.left n
  exact (universalNativeFamily_roots_iff A n M p r e).mp
    (Universal.IntrinsicFamily.Construction.universal_native_family_from_TorsionQuotient_FiniteDescent A n hn hcop M p r (MultiplicativeChoiceKernel.Construction.blockPairingsToRoots n s p r e)
      hsep scalar hscalar h_TorsionQuotient h_FiniteDescent)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeIntrinsicFamily.Construction

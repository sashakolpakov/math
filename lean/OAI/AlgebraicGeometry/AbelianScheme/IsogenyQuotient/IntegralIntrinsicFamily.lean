import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.IntrinsicFamily
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryModules

/-! # Integral Intrinsic Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralIntrinsicFamily.Construction

noncomputable section

/-!
Specialize the native universal family to the multiplier `q ^ h` and the
three bounded elementary exponents on each chosen block.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem universal_integral_native_family_from_TorsionQuotient_FiniteDescent
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T)
    (q : ℕ) (hq : q.Prime) (hcop : Nat.Coprime q N) (h : ℕ)
    (a : Fin s → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h)
    (chosen opposite : Fin s → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (chosen i)] [∀ i, IsMonHom (opposite i)]
    {W : Over T.left} [GrpObj W] [Etale W.hom] [IsSeparated W.hom]
    (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock (q ^ h) (chosen i))
      (B := OppositeKernel.Construction.torsionBlock (q ^ h) (opposite i)) (W := W))
    (hsep : ∀ i j : ChoiceKernel.Construction.KernelIndex s, i ≠ j →
      Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (ChoiceKernel.Construction.choiceKernelProjector s chosen opposite j) ≫
        Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (ChoiceKernel.Construction.choiceKernelProjector s chosen opposite i) = 1)
    (scalar : NumberField.RingOfIntegers E → ChoiceKernel.Construction.KernelIndex s → ℤ)
    (hscalar : ∀ b i, OppositeKernel.Construction.torsionBlockInclusion (q ^ h) (ChoiceKernel.Construction.choiceKernelProjector s chosen opposite i) ≫
      A.action.map b =
        (OppositeKernel.Construction.torsionBlockInclusion (q ^ h) (ChoiceKernel.Construction.choiceKernelProjector s chosen opposite i)) ^ scalar b i)
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{0})
    (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) :
    letI : NeZero q := ⟨hq.ne_zero⟩
    letI : ∀ v, Module (ZMod (q ^ h)) (ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) :=
      fun v => ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
    Universal.IntrinsicFamily.Construction.UniversalNativeFamily A (q ^ h) (fun v => ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))
      chosen opposite e := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let : ∀ v, Module (ZMod (q ^ h)) (ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) :=
    fun v => ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
  exact Universal.IntrinsicFamily.Construction.universal_native_family_from_TorsionQuotient_FiniteDescent A (q ^ h) (pow_pos hq.pos h) (hcop.pow_left h)
    (fun v => ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) chosen opposite e hsep scalar hscalar h_TorsionQuotient h_FiniteDescent

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralIntrinsicFamily.Construction

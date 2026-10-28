import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralIntrinsicFamily

/-! # Points Intrinsic Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction

noncomputable section

/-!
Genuine split residue coordinates supply the integral projector maps, their
orthogonality, and their scalar restrictions in the universal quotient
construction. These equations are no longer separate inputs.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

section Projectors

variable {E F : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field F] [NumberField F] {κ : F →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice F κ q) (iota : E →+* F) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (h s : ℕ) (labels : ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))

abbrev l45ChosenProjectors : Fin s → (A.scheme ⟶ A.scheme) :=
  fun v => σ.map (j.projector iota hsplit h (labels (Sum.inl v)))

abbrev l45OppositeProjectors : Fin s → (A.scheme ⟶ A.scheme) :=
  fun v => σ.map (j.projector iota hsplit h (labels (Sum.inr v)))

theorem l45ChoiceKernelProjector_eq (i : ChoiceKernel.Construction.KernelIndex s) :
    ChoiceKernel.Construction.choiceKernelProjector s (l45ChosenProjectors j iota hsplit A σ h s labels)
      (l45OppositeProjectors j iota hsplit A σ h s labels) i =
      σ.map (j.projector iota hsplit h (labels i)) := by
  cases i <;> rfl

end Projectors

/-- The universal quotient, action, full marking, and Lie signature are
constructed using the actual CMPoints projector lifts. -/
theorem universal_integral_native_family_from_CMPoints_coordinates
    {E K F : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    [Field F] [NumberField F] {κ : F →+* ℂ}
    {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T)
    (q : ℕ) [Fact q.Prime] (hcop : Nat.Coprime q N) (h : ℕ)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice F κ q) (arithmeticEmbedding : E →+* F)
    (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
    (labels : ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
    (a : Fin s → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h)
    {W : Over T.left} [GrpObj W] [Etale W.hom] [IsSeparated W.hom]
    (e : ∀ i, Annihilator.Construction.SchemeBicharacter
      (A := OppositeKernel.Construction.torsionBlock (q ^ h)
        (l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels i))
      (B := OppositeKernel.Construction.torsionBlock (q ^ h)
        (l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels i))
    (W := W))
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{0})
    (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) :
    letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    letI : ∀ v, Module (ZMod (q ^ h)) (ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) :=
      fun v => ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
    Universal.IntrinsicFamily.Construction.UniversalNativeFamily A (q ^ h) (fun v => ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))
      (l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels)
      (l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels) e := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  let : ∀ v, Module (ZMod (q ^ h)) (ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) :=
    fun v => ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
  apply IntegralIntrinsicFamily.Construction.universal_integral_native_family_from_TorsionQuotient_FiniteDescent A q Fact.out hcop h a ha _ _ e
    (scalar := fun b i => ((j.residueCharacter arithmeticEmbedding (labels i) h b).val : ℤ))
    (h_TorsionQuotient := h_TorsionQuotient) (h_FiniteDescent := h_FiniteDescent)
  · intro i k hik
    have hh := PointsProjectorSum.Construction.l45_native_projectors_orthogonal j arithmeticEmbedding hsplit A.polarized.abelian
      A.action h (labels k) (labels i) (fun he => hik (labels.injective he).symm)
    cases i <;> cases k <;> exact hh
  · intro b i
    have hh := PointsProjectorSum.Construction.l45_native_projector_scalar j arithmeticEmbedding hsplit A.polarized.abelian A.action h (labels i) b
    cases i <;> exact hh

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction

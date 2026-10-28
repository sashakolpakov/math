import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexTarget
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceMultisets

/-! # Hecke Targets -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.HeckeTargets.Construction

noncomputable section

/-! Raw integral Hecke target maps on all complex points of the full
fine PEL model. Each raw coset contributes once, with repeated targets
retained. No Noetherian assumption is made on the moduli scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
  {d N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)
  {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
  (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
  (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
  (h : ℕ) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime q (∏ i, P.polarizationType i))
  (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) {c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)}

def originalRawHeckeTarget (x : Over.mk c ⟶ Z.space)
    (g : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant))) :
    Over.mk c ⟶ Z.space := by
  letI : ∀ v, Module (ZMod (q ^ h)) (ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) :=
    fun v => ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
  exact ComplexTarget.Construction.originalComplexRawTarget (Z.universal.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels
    (fun v => ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) a ha hdominant (fun _ => AddEquiv.ulift)
    hcop ((hpol.pow_right 2).pow_left h) hlabels h_FiniteDescent Z hZ g

def originalRawHeckeMultiset (x : Over.mk c ⟶ Z.space) : Multiset (Over.mk c ⟶ Z.space) :=
  ChoiceMultisets.Construction.rawSplitTargetMultiset d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)
    (originalRawHeckeTarget Z hZ j arithmeticEmbedding hsplit hd hdegree h labels hlabels a ha hdominant
      hcop hpol h_FiniteDescent x)

theorem originalRawHeckeMultiset_card (x : Over.mk c ⟶ Z.space) :
    (originalRawHeckeMultiset Z hZ j arithmeticEmbedding hsplit hd hdegree h labels hlabels a ha hdominant
      hcop hpol h_FiniteDescent x).card =
      Nat.card (Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant))) :=
  CorrespondenceFibers.Construction.finiteTargetMultiset_card _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.HeckeTargets.Construction

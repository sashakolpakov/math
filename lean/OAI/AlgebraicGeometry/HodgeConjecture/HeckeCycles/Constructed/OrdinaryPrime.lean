import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.IntrinsicReduction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LabeledGoodPrime

/-! # Ordinary Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.OrdinaryPrime.CM.Ordinary

noncomputable section

/-! Choose arbitrarily large split ordinary primes from the complete
named inputs, retaining all excluded primes and auxiliary fields. The
same actual models carry the constructed good-prime and native reduction
data; no ordinary splitting or operator matching is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM

universe u v

/-- Complete splitting is preserved by an isomorphism of number fields. -/
private theorem splitsCompletelyAt_of_ringEquiv
    {F G : Type*} [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃+* G) {q : ℕ}
    (h : PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt F q) :
    PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt G q := by
  obtain ⟨h⟩ := h
  let eInt := NumberField.RingOfIntegers.mapRingEquiv e
  have hIdeal : Ideal.span ({(q : NumberField.RingOfIntegers G)} : Set _) =
      (Ideal.span ({(q : NumberField.RingOfIntegers F)} : Set _)).map eInt.toRingHom := by
    simp [Ideal.map_span]
  have hdim : Module.finrank ℚ F = Module.finrank ℚ G :=
    e.toRatAlgEquiv.toLinearEquiv.finrank_eq
  unfold PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt
  rw [← hdim]
  exact ⟨(Ideal.quotientEquiv _ _ eInt hIdeal).symm.trans h⟩

/-- Lifting the finite index type and its fields recovers the same input
for families in the base universe. -/
private theorem cmPointsInput_base
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{u, v}) :
    AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0} := by
  intro E K _ _ _ _ _ _ _ M hM I _ L _ _ excluded bound
  let fields : ULift.{u} I → Type v := fun i => ULift.{v} (L i.down)
  let (i : ULift.{u} I) : NumberField (fields i) :=
    NumberField.of_ringEquiv (L i.down) (fields i)
      (ULift.ringEquiv : fields i ≃+* L i.down).symm
  obtain ⟨q, hq, hb, hex, hE, hK, hExt, hL, j, hsplit, R, hgeom⟩ :=
    hCMPoints E K M hM fields excluded bound
  refine ⟨q, hq, hb, hex, hE, hK, hExt, ?_, j, hsplit, R, hgeom⟩
  intro i
  exact splitsCompletelyAt_of_ringEquiv
    (ULift.ringEquiv : fields ⟨i⟩ ≃+* L i) (hL ⟨i⟩)

def Conclusion
    (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
    (E K : Type) [Field E] [NumberField E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {I : Type u} [Fintype I] (L : I → Type v) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) : Prop :=
    ∃ (q : ℕ) (hq : q.Prime),
      let _ : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt K q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ (j : M.QadicChoice q) (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
        (R : M.GoodIntegralReduction q j), AbelianScheme.FrobeniusKernel.CMPoints.Construction.GeometricConclusion R ∧
        ∃ labels : (Fin M.s × Bool) ≃ Gal(E/ℚ),
          ∃ hlabels : ∀ (w : Fin M.s) (b : Bool),
            labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b),
            labels (⟨0, hM.1⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E ∧
            (∀ (a : M.Family)
              (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
                ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver)),
              (Witt.PELSource.CM.heckeData M a C
                (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime) ∧
            ∀ a : M.Family,
              let D := FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a
              ∃ (Y : D.OrdinaryPoint → Multiset D.OrdinaryPoint) (Z : D.OrdinaryPoint → D.OrdinaryPoint),
                Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a
                  (LabeledGoodPrime.CM.denominator_coprime M j R)
                  ⟨0, hM.1⟩ (IntrinsicReduction.CM.Intrinsic.multiplicative M hM labels a) hTorsionQuotient Z Y ∧
                (∀ x, (Y x).map D.ordinaryFrobenius = Y (D.ordinaryFrobenius x)) ∧
                (∀ x, D.ordinaryFrobenius (Z x) = Z (D.ordinaryFrobenius x))

theorem exists_prime
    (hNeighborCounting : Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{u, v}) (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (E K : Type) [Field E] [NumberField E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {I : Type u} [Fintype I] (L : I → Type v) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    Conclusion hTorsionQuotient E K M hM L excluded bound := by
  obtain ⟨q, hq, hb, hex, hE, hK, hExt, hL, j, hsplit, R, hgeom⟩ :=
    hCMPoints E K M hM L excluded bound
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨labels, hlabels, hactive, hred⟩ :=
    IntrinsicReduction.CM.Intrinsic.exists_reductions M hM j hsplit R
      hNeighborCounting hFrobeniusKernel (cmPointsInput_base hCMPoints) hCartierDuality hTorsionQuotient hgeom (LabeledGoodPrime.CM.denominator_coprime M j R)
  exact ⟨q, hq, hb, hex, hE, hK, hExt, hL, j, hsplit, R, hgeom,
    labels, hlabels, hactive, fun a C =>
      LabeledGoodPrime.CM.good_prime M j R labels a C hsplit hlabels, hred⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.OrdinaryPrime.CM.Ordinary

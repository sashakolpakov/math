import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCoefficientPerfection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PerfectAnnihilatorModels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents

/-! # Reduced Kernel Models -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedKernelModels

noncomputable section

/-! Construct complete integral multiplier kernels from the actual
active finite flat subgroup. Geometry, separation and the canonical
opposite-annihilator models are all derived from the original source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCoefficientPerfection
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PerfectAnnihilatorModels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock.Intrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents

variable {S : Scheme} [IsReduced S] [IsLocallyNoetherian S] {g N s : ℕ} {δ : Fin g → ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hdegree : q.Coprime (∏ i, δ i))
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin s, labels (.inr v) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (.inl v))
  (n : ℕ) (active : Fin s) (multiplicative : Fin s → Bool)
  {P : Over S} (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.abelian.scheme P) (R : F.Model)
  (hF : F.KilledBy (q ^ n))
  (hFs : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels active))

abbrev reducedNativeBlockPairings (v : Fin s) :=
  ReducedCoefficientPerfection.reducedCanonicalCoefficientPairing j iota hsplit A ρ n (labels (.inl v)) (labels (.inr v))

def reducedNativeFullKernelModel :
    (Kernel.Models.multiplierFullKernel (q ^ n)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A.abelian ρ n s labels)
      (reducedNativeBlockPairings j iota hsplit A ρ labels n) active multiplicative F).Model := by
  have geometry (v : Fin s) := IntegralIntrinsicBlock.Intrinsic.integralNativeBlock_finiteLocallyFree j iota hsplit A ρ n (labels (.inl v))
  let : ∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v)).hom := fun v => (geometry v).1
  let : ∀ v, Flat (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v)).hom := fun v => (geometry v).2.1
  let : ∀ v, LocallyOfFinitePresentation (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v)).hom := fun v => (geometry v).2.2
  apply Kernel.Models.multiplierFullKernel_model (q ^ n)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A.abelian ρ n s labels)
    (reducedNativeBlockPairings j iota hsplit A ρ labels n) active multiplicative F R hF hFs
  · intro v w hvw
    exact Intrinsic.AllKernelComponents.native_label_separation j iota hsplit A.abelian ρ labels n (.inl w) (.inl v)
      (fun h => hvw (Sum.inl.inj h).symm)
  · intro v w
    exact Intrinsic.AllKernelComponents.native_label_separation j iota hsplit A.abelian ρ labels n (.inr w) (.inl v)
      (by intro h; cases h)
  · intro v w
    exact Intrinsic.AllKernelComponents.native_label_separation j iota hsplit A.abelian ρ labels n (.inl w) (.inr v)
      (by intro h; cases h)
  · intro v w hvw
    exact Intrinsic.AllKernelComponents.native_label_separation j iota hsplit A.abelian ρ labels n (.inr w) (.inr v)
      (fun h => hvw (Sum.inr.inj h).symm)
  · intro v
    exact PerfectAnnihilatorModels.annihilatorModelInput_of_perfect (P := P) (q ^ n)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A.abelian ρ n s labels v)
      (reducedNativeBlockPairings j iota hsplit A ρ labels n v)
      (ReducedCoefficientPerfection.reducedCanonicalCoefficientPairing_isPerfect j iota hsplit A ρ hρ hdegree n
        (labels (.inl v)) (labels (.inr v)) (hlabels v))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedKernelModels

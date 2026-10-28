import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalQuotientKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport

/-! # Normalized Integral Quotient Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedIntegralQuotientKernel

noncomputable section

/-! Normalize the actual integral quotient kernel before substituting
the constructed original evaluation field and finite flat subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalQuotientKernel

local instance normalizedQuotientPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

variable {S : Scheme} [IsReduced S] [IsLocallyNoetherian S] {g N s : ℕ} {δ : Fin g → ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hdegree : q.Coprime (∏ i, δ i))
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin s, labels (.inr v) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (.inl v))
  (n : ℕ) (hn : 1 ≤ n) (active : Fin s) (multiplicative : Fin s → Bool)
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (ρ.map (j.projector iota hsplit 1 (labels (.inl active))))))

attribute [local irreducible] Kernel.Base.fullKernel AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion

def integralCanonicalQuotient_normalizedKernelIdentity {T : Scheme} (b : T ⟶ S) := by
  have h := IntegralCanonicalQuotientKernel.integralCanonicalQuotient_pullback_nativeKernel j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative H b
  unfold IntegralCanonicalNeighbors.integralCanonicalFullKernel Kernel.Models.multiplierFullKernel
    ReducedKernelModels.reducedNativeBlockPairings
    ReducedCoefficientPerfection.reducedCanonicalCoefficientPairing IntegralCanonicalNeighbors.integralActiveFamily at h
  try dsimp (config := { instances := true }) only at h
  exact PLift.up h

def integralCanonicalQuotient_pulledKernelIdentity {T : Scheme} (b : T ⟶ S)
    {G : Grp (Over T)}
    (e : G ⟶ (Over.pullback b).mapGrp.obj (Grp.mk A.abelian.scheme)) := by
  have h := (integralCanonicalQuotient_normalizedKernelIdentity
    j iota hsplit A ρ hρ hdegree labels hlabels n hn active multiplicative H b).down
  exact PLift.up (congrArg (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom.hom) h)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedIntegralQuotientKernel

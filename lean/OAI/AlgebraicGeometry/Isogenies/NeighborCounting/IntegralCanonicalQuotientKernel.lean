import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralKernelParameterChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientBaseChangeKernel

/-! # Integral Canonical Quotient Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalQuotientKernel

noncomputable section

/-! The actual complete integral canonical quotient has exactly the
expected full kernel on its generic fiber, including all compact and
opposite blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralKernelParameterChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientBaseChangeKernel.Identity

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

theorem integralCanonicalQuotient_pullback_nativeKernel {T : Scheme} (b : T ⟶ S) :
    AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel
      ((IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
        n hn active multiplicative (Over.mk (𝟙 S)) H).identitySourceIsogeny.pullback b).hom =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.abelian.scheme) (Over.mk b)
        (IntegralCanonicalNeighbors.integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative (Over.mk b) H) := by
  let c : Over.mk b ⟶ Over.mk (𝟙 S) := Over.homMk b (Category.comp_id b)
  have hp := IntegralKernelParameterChange.integralCanonicalFullKernel_parameter_baseChange j iota hsplit A ρ labels
    n active multiplicative c H
  exact (QuotientBaseChangeKernel.Identity.identitySourceIsogeny_pullback_nativeKernel
    (IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
      n hn active multiplicative (Over.mk (𝟙 S)) H) b).trans
        (congrArg (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.abelian.scheme) (Over.mk b)) hp)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalQuotientKernel

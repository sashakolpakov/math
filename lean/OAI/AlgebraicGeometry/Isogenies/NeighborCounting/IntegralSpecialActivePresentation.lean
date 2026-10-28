import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialChosenKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.SubgroupComparisons

/-! # Integral Special Active Presentation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialActivePresentation

noncomputable section

/-! Express the chosen active special kernel by the actual pullback of
its finite flat carrier and its original ambient inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialChosenKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.SubgroupComparisons
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

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

variable {T : Scheme} (b : T ⟶ S)

theorem integralSpecial_active_factor (U : Over T) (x : U ⟶ (A.abelian.pullback b).scheme)
    (hx : x ≫ (Over.pullback b).map
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels active) = x) :
    x ≫ ((IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
      n hn active multiplicative (Over.mk (𝟙 S)) H).identitySourceIsogeny.pullback b).hom = 1 ↔
      ∃ z : U ⟶ (Over.pullback b).obj H.carrier,
        z ≫ (Over.pullback b).map
          (H.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1)
            (ρ.map (j.projector iota hsplit 1 (labels (.inl active))))) = x := by
  have h := IntegralSpecialChosenKernel.integralSpecial_active_kernel j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative H b U x hx
  let k : Grp.mk H.carrier ⟶ Grp.mk A.abelian.scheme :=
    Grp.homMk (EmbeddedActiveFamilies.embeddedActiveMap (q ^ 1)
      (ρ.map (j.projector iota hsplit 1 (labels (.inl active)))) H)
  have hk := Parameter.SubgroupComparisons.relativeParameter_fixed_kernel (Grp.mk H.carrier) (Grp.mk A.abelian.scheme) (Over.mk b) k
  have hp := congrArg (fun F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (A.abelian.pullback b).scheme (Over.mk (𝟙 T)) =>
    x ∈ F.points U (toUnit U)) hk
  exact h.trans (Iff.of_eq hp)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialActivePresentation

import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor

/-! # Prime Projector Support -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeProjectorSupport

noncomputable section

/-! The native higher projector and the prime-level projector act
identically on any subgroup already proved to be killed by q. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  {P : Over S} (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (n : ℕ) (hn : 1 ≤ n) (τ : Gal(E/ℚ))

include hn in
theorem prime_projector_supported (hk : F.KilledBy q)
    (hs : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (ρ.map (j.projector iota hsplit n τ))) :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (ρ.map (j.projector iota hsplit 1 τ)) := by
  intro X t a ha
  have hk' : a ^ (q ^ 1) = 1 := by simpa only [pow_one] using hk X t a ha
  have he := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A ρ _ _ (q ^ 1)
    (by simpa only [Nat.cast_pow] using ProjectorLevels.projector_level_congruence j iota hsplit hn τ) X a hk'
  exact he.symm.trans (hs X t a ha)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeProjectorSupport

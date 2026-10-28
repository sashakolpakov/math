import OAI.AlgebraicGeometry.Divisors.LineBundles.CycleLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelationLifting

/-! # Chow Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: exact localization for the genuine rational Chow quotients

For a closed complement and its actual open inclusion, closed pushforward
has image precisely the kernel of open restriction. The proof lifts the
open rational-equivalence relation, subtracts that ambient relation, and
then lifts the complete remaining cycle to the closed complement.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {U X Z : Scheme} [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z]
    (i : U ⟶ X) [IsOpenImmersion i] (j : Z ⟶ X) [IsClosedImmersion j]
    (hcomp : Set.range j = (Set.range i)ᶜ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include hcomp

theorem openChowRestriction_closed (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ (j ≫ f) d) :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d (Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d a) = 0 := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (j ≫ f) d a
  rw [Closed.ChowPushforward.BundleCycles.closedChowPushforward_cycle, Open.ChowRestriction.BundleCycles.openChowRestriction_cycle,
    CycleLocalization.BundleCycles.openDimensionCycleRestriction_closed i j hcomp f d, map_zero]

/-- Exactness at the Chow group of the ambient scheme. -/
theorem openChowRestriction_eq_zero_iff (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d a = 0 ↔ a ∈ LinearMap.range (Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d) := by
  constructor
  · intro ha
    obtain ⟨z, hza, hz⟩ := Open.RelationLifting.BundleCycles.openChowRestriction_exists_zero_restriction i f d a ha
    obtain ⟨w, hw⟩ := CycleLocalization.BundleCycles.exists_closedDimensionCycle_of_zero_restriction i j hcomp f d z hz
    refine ⟨DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d w, ?_⟩
    rw [Closed.ChowPushforward.BundleCycles.closedChowPushforward_cycle, hw, hza]
  · rintro ⟨b, rfl⟩
    exact openChowRestriction_closed i j hcomp f d b

/-- The actual closed/open Chow localization sequence is exact. -/
theorem chowLocalization_exact (d : ℕ) :
    LinearMap.range (Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d) = LinearMap.ker (Open.ChowRestriction.BundleCycles.openChowRestriction i f d) := by
  ext a
  exact (openChowRestriction_eq_zero_iff i j hcomp f d a).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization.BundleCycles

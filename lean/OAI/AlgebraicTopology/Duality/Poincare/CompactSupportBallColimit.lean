import OAI.AlgebraicTopology.Duality.Poincare.CompactBallExhaustion
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCofinal

/-! # Compact Support Ball Colimit -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportBallColimit

noncomputable section

/-!
# Computing Euclidean compact support using closed balls

Closed balls of radii `j + 1` form the actual support stages in the colimits
below. Every compact-support cohomology class is represented at such a stage,
and a stage class vanishes precisely when it vanishes in a later ball stage.
These statements concern the existing relative singular cohomology groups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Closed integer-radius balls compute the actual compact-support cochain complex. -/
def compactSupportCochainBallIso :
    colimit (CompactBallExhaustion.compactBallExhaustionFunctor E ⋙
      CompactSupportCohomology.compactSupportCochainDiagram M (TopCat.of E)) ≅
        CompactSupportCohomology.compactSupportedCochains M (TopCat.of E) :=
  CompactSupportCofinal.compactSupportCochainCofinalIso M (TopCat.of E) (CompactBallExhaustion.compactBallExhaustionFunctor E)

@[reassoc (attr := simp)]
theorem compactSupportCochainBallIso_ι (j : ℕ) :
    colimit.ι (CompactBallExhaustion.compactBallExhaustionFunctor E ⋙
        CompactSupportCohomology.compactSupportCochainDiagram M (TopCat.of E)) j ≫
        (compactSupportCochainBallIso M E).hom =
      CompactSupportCohomology.compactSupportCochainι M (TopCat.of E) (CompactBallExhaustion.compactBallSupport E j) :=
  CompactSupportCofinal.compactSupportCochainCofinalIso_ι M (TopCat.of E) (CompactBallExhaustion.compactBallExhaustionFunctor E) j

/-- Relative cohomology on the closed-ball stages computes actual Euclidean `Hc`. -/
def compactSupportCohomologyBallIso (n : ℕ) :
    colimit (CompactBallExhaustion.compactBallExhaustionFunctor E ⋙
      CompactSupportCohomology.compactSupportCohomologyDiagram M (TopCat.of E) n) ≅
        CompactSupportCohomology.compactSupportedCohomology M (TopCat.of E) n :=
  CompactSupportCofinal.compactSupportCohomologyCofinalIso M (TopCat.of E) (CompactBallExhaustion.compactBallExhaustionFunctor E) n

@[reassoc (attr := simp)]
theorem compactSupportCohomologyBallIso_ι (n j : ℕ) :
    colimit.ι (CompactBallExhaustion.compactBallExhaustionFunctor E ⋙
        CompactSupportCohomology.compactSupportCohomologyDiagram M (TopCat.of E) n) j ≫
        (compactSupportCohomologyBallIso M E n).hom =
      CompactSupportCohomology.compactSupportCohomologyι M (TopCat.of E) (CompactBallExhaustion.compactBallSupport E j) n :=
  CompactSupportCofinal.compactSupportCohomologyCofinalIso_ι M (TopCat.of E) (CompactBallExhaustion.compactBallExhaustionFunctor E) n j

/-- Every actual compact-support cohomology class has a representative on a closed ball. -/
theorem compactSupportedCohomology_exists_ball_stage (n : ℕ)
    (c : CompactSupportCohomology.compactSupportedCohomology M (TopCat.of E) n) :
    ∃ (j : ℕ) (a : Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of E)
      (CompactBallExhaustion.compactBallSupport E j : Set E)ᶜ n),
      CompactSupportCohomology.compactSupportCohomologyι M (TopCat.of E) (CompactBallExhaustion.compactBallSupport E j) n a = c := by
  obtain ⟨K, a, ha⟩ := CompactSupportColimit.compactSupportedCohomology_exists_stage M (TopCat.of E) n c
  obtain ⟨j, hj⟩ := CompactBallExhaustion.exists_le_compactBallSupport E K
  refine ⟨j, CompactSupportColimit.compactSupportCohomologyMap M hj n a, ?_⟩
  change (CompactSupportColimit.compactSupportCohomologyMap M hj n ≫
    CompactSupportCohomology.compactSupportCohomologyι M (TopCat.of E) (CompactBallExhaustion.compactBallSupport E j) n) a = c
  rw [CompactSupportColimit.compactSupportCohomologyMap_ι, ha]

/-- Vanishing of a ball-stage class is detected by enlargement to a later actual ball. -/
theorem compactSupportCohomology_ball_stage_eq_zero_iff (n i : ℕ)
    (a : Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of E)
      (CompactBallExhaustion.compactBallSupport E i : Set E)ᶜ n) :
    CompactSupportCohomology.compactSupportCohomologyι M (TopCat.of E) (CompactBallExhaustion.compactBallSupport E i) n a = 0 ↔
      ∃ (j : ℕ) (h : i ≤ j),
        CompactSupportColimit.compactSupportCohomologyMap M (CompactBallExhaustion.compactBallSupport_mono E h) n a = 0 := by
  constructor
  · intro h
    obtain ⟨L, hL, ha⟩ :=
      (CompactSupportColimit.compactSupportCohomologyι_eq_zero_iff M (TopCat.of E) n a).mp h
    obtain ⟨j, hj⟩ := CompactBallExhaustion.exists_le_compactBallSupport E L
    have hLk : L ≤ CompactBallExhaustion.compactBallSupport E (max i j) :=
      hj.trans (CompactBallExhaustion.compactBallSupport_mono E (Nat.le_max_right i j))
    refine ⟨max i j, Nat.le_max_left i j, ?_⟩
    have hmap : CompactSupportColimit.compactSupportCohomologyMap M (hL.trans hLk) n a = 0 := by
      rw [← CompactSupportColimit.compactSupportCohomologyMap_comp]
      change CompactSupportColimit.compactSupportCohomologyMap M hLk n
        (CompactSupportColimit.compactSupportCohomologyMap M hL n a) = 0
      rw [ha, map_zero]
    exact hmap
  · rintro ⟨j, h, ha⟩
    exact (CompactSupportColimit.compactSupportCohomologyι_eq_zero_iff M (TopCat.of E) n a).mpr
      ⟨CompactBallExhaustion.compactBallSupport E j, CompactBallExhaustion.compactBallSupport_mono E h, ha⟩

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportBallColimit

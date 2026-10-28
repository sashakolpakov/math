import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledGeneratorFamily
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountReduction
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BoundaryAuxiliaryOrder

/-! # Family Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FamilyTransform.Construction

noncomputable section

/-! Exact individual boundary equations and boundary-count behavior on actual blowup charts. -/

universe u

variable {R ι : Type u} [CommRing R]

/-- Divide each selected old boundary equation once by the actual
exceptional parameter, retaining its original index. -/
def blowupBoundaryFamily (I : Ideal R) (a : I) (w : ι → R) (hw : ∀ i, w i ∈ I) :
    ι → Blowup.Charts.Construction.blowupChart I a := fun i => ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w i, hw i⟩

theorem blowupBoundaryFamily_factorization (I : Ideal R) (a : I) (w : ι → R)
    (hw : ∀ i, w i ∈ I) (i : ι) :
    Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val * blowupBoundaryFamily I a w hw i :=
  (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a ⟨w i, hw i⟩).symm

/-- The separately divided old equations generate exactly the actual
control-one transform of their intersection ideal. -/
theorem blowupBoundaryFamily_controlledIdeal (I : Ideal R) (a : I) (w : ι → R)
    (hw : ∀ i, w i ∈ I) :
    ControlledTransform.Construction.blowupControlledTransform I (Ideal.span (Set.range w)) 1 a =
      Ideal.span (Set.range (blowupBoundaryFamily I a w hw)) := by
  change ((Ideal.span (Set.range w)).map (Blowup.Charts.Construction.blowupChartConstants I a)).colon
    (Ideal.span {Blowup.Charts.Construction.blowupChartConstants I a a.val ^ 1}) = _
  rw [pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val)]
  exact ControlledGeneratorFamily.Construction.span_map_colon_eq_span_of_factor _ w _ _ (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
    (blowupBoundaryFamily_factorization I a w hw)

/-- An old boundary active after division was already active at the
image point. No new exceptional component is included in this old count. -/
theorem blowupBoundaryFamily_active_subset (I : Ideal R) (a : I) (w : ι → R)
    (hw : ∀ i, w i ∈ I) (B : Finset ι) (q : Ideal (Blowup.Charts.Construction.blowupChart I a)) :
    CountReduction.Construction.activeBoundaryComponents (blowupBoundaryFamily I a w hw) B q ⊆
      CountReduction.Construction.activeBoundaryComponents w B (q.comap (Blowup.Charts.Construction.blowupChartConstants I a)) := by
  classical
  intro i hi
  obtain ⟨hiB, hiq⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨hiB, ?_⟩
  change Blowup.Charts.Construction.blowupChartConstants I a (w i) ∈ q
  rw [blowupBoundaryFamily_factorization I a w hw i]
  exact q.mul_mem_left _ hiq

theorem blowupBoundaryFamily_active_count_le (I : Ideal R) (a : I) (w : ι → R)
    (hw : ∀ i, w i ∈ I) (B : Finset ι) (q : Ideal (Blowup.Charts.Construction.blowupChart I a)) :
    (CountReduction.Construction.activeBoundaryComponents (blowupBoundaryFamily I a w hw) B q).card ≤
      (CountReduction.Construction.activeBoundaryComponents w B (q.comap (Blowup.Charts.Construction.blowupChartConstants I a))).card :=
  Finset.card_le_card (blowupBoundaryFamily_active_subset I a w hw B q)

/-- Clearing the selected boundary ideal gives strict decrease of the
number of active selected old components at every high-order prime. -/
theorem boundary_clearance_active_count_lt (k : Type u) [CommRing k] [Algebra k R]
    (J : Ideal R) (w : ι → R) (B : Finset ι) (m : ℕ) (hm : 0 < m)
    (hclear : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m - 1) ⊔ CountReduction.Construction.boundaryIntersectionIdeal w B = ⊤)
    (q : Ideal R) [q.IsPrime]
    (hJ : J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ m) :
    (CountReduction.Construction.activeBoundaryComponents w B q).card < B.card := by
  classical
  apply Nat.lt_of_not_ge
  intro hcard
  have heq : CountReduction.Construction.activeBoundaryComponents w B q = B :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard
  apply Smooth.BoundaryAuxiliaryOrder.Construction.boundary_auxiliary_clearance_at_every_prime k J _ m hm hclear q hJ
  apply (CountReduction.Construction.boundaryIntersectionIdeal_le_iff w B q).mpr
  intro i hi
  have hia : i ∈ CountReduction.Construction.activeBoundaryComponents w B q := heq.symm ▸ hi
  exact (Finset.mem_filter.mp hia).2

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FamilyTransform.Construction

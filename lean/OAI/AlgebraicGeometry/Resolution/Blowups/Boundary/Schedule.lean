import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialSchedule
import OAI.AlgebraicGeometry.Resolution.Blowups.LabelledBoundaryMonomialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountReduction
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep

/-! # Schedule -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Schedule.Construction

noncomputable section

/-! The common combinatorial face update holds on actual boundary-intersection blowup charts. -/

universe u v

/-- Every set of boundary components through a point is contained in a recorded face. -/
def BoundaryFacesCover {R : Type u} [CommRing R] {ι : Type v}
    (w : ι → R) (L : List (Finset ι)) : Prop :=
  ∀ p : PrimeSpectrum R, ∃ S ∈ L, ∀ j, w j ∈ p.asIdeal → j ∈ S

theorem boundaryFacesCover_univ {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (w : ι → R) : BoundaryFacesCover w [Finset.univ] :=
  fun _ => ⟨Finset.univ, List.mem_singleton_self _, fun _ _ => Finset.mem_univ _⟩

theorem BoundaryFacesCover.map {R A : Type u} [CommRing R] [CommRing A] {ι : Type v}
    {w : ι → R} {L : List (Finset ι)} (h : BoundaryFacesCover w L) (f : R →+* A) :
    BoundaryFacesCover (fun j => f (w j)) L := by
  intro p
  obtain ⟨S, hS, hw⟩ := h (PrimeSpectrum.comap f p)
  exact ⟨S, hS, hw⟩

theorem BoundaryFacesCover.mul_units {R : Type u} [CommRing R] {ι : Type v}
    {w : ι → R} {L : List (Finset ι)} (h : BoundaryFacesCover w L)
    (v : ι → R) (hv : ∀ j, IsUnit (v j)) : BoundaryFacesCover (fun j => v j * w j) L := by
  intro p
  obtain ⟨S, hS, hw⟩ := h p
  exact ⟨S, hS, fun j hj => hw j ((p.asIdeal.unit_mul_mem_iff_mem (hv j)).mp hj)⟩

def boundaryIntersectionGenerator {R : Type u} [CommRing R] {ι : Type v}
    (w : ι → R) (C : Finset ι) (i : C) : CountReduction.Construction.boundaryIntersectionIdeal w C :=
  ⟨w i.val, Ideal.subset_span ⟨i, rfl⟩⟩

theorem boundaryIntersection_mem {R : Type u} [CommRing R] {ι : Type v}
    (w : ι → R) (C : Finset ι) (j : ι) (hj : j ∈ C) :
    w j ∈ CountReduction.Construction.boundaryIntersectionIdeal w C := Ideal.subset_span ⟨⟨j, hj⟩, rfl⟩

theorem blowupMixedBoundaryFamily_denominator_one {R : Type u} [CommRing R] {ι : Type v}
    (w : ι → R) (C : Finset ι) (i : C) :
    MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (CountReduction.Construction.boundaryIntersectionIdeal w C) (boundaryIntersectionGenerator w C i)
      C w (boundaryIntersection_mem w C) (some i.val) = 1 := by
  classical
  rw [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_left i.property]
  exact Etale.CoefficientStep.Construction.blowupChartRatio_self _ _

theorem BoundaryFacesCover.blowup_intersection {R : Type u} [CommRing R]
    {ι : Type v} [DecidableEq ι] {w : ι → R} {L : List (Finset ι)}
    (h : BoundaryFacesCover w L) (C : Finset ι) (i : C) :
    BoundaryFacesCover
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (CountReduction.Construction.boundaryIntersectionIdeal w C) (boundaryIntersectionGenerator w C i)
        C w (boundaryIntersection_mem w C)) (MonomialSchedule.Construction.boundaryScheduleFaces C L) := by
  classical
  let I := CountReduction.Construction.boundaryIntersectionIdeal w C
  let d := boundaryIntersectionGenerator w C i
  let v := MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d C w (boundaryIntersection_mem w C)
  let f := Blowup.Charts.Construction.blowupChartConstants I d
  intro p
  obtain ⟨S, hS, hw⟩ := h (PrimeSpectrum.comap f p)
  have hsome (j : ι) (hj : v (some j) ∈ p.asIdeal) : j ∈ S := by
    apply hw j
    change f (w j) ∈ p.asIdeal
    rw [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily_factorization I d C w (boundaryIntersection_mem w C) j]
    exact p.asIdeal.mul_mem_left _ hj
  have hiunit : v (some i.val) = 1 := blowupMixedBoundaryFamily_denominator_one w C i
  by_cases hCS : C ⊆ S
  · refine ⟨MonomialSchedule.Construction.boundaryExceptionalFace S i.val, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨S, hS, ?_⟩
      rw [MonomialSchedule.Construction.boundaryFaceBranches, ite_eq_left hCS]
      exact List.mem_map.mpr ⟨i.val, Finset.mem_toList.mpr i.property, rfl⟩
    · intro j hj
      cases j with
      | none => exact Finset.mem_insert_self _ _
      | some j =>
          have hji : j ≠ i.val := by
            intro he
            subst j
            change v (some i.val) ∈ p.asIdeal at hj
            rw [hiunit] at hj
            exact p.asIdeal.notMem_of_isUnit isUnit_one hj
          apply Finset.mem_insert_of_mem
          exact Finset.mem_map.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hsome j hj⟩, rfl⟩
  · have hn : v none ∉ p.asIdeal := by
      intro hn
      apply hCS
      intro j hj
      apply hw j
      change f (w j) ∈ p.asIdeal
      rw [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily_factorization I d C w (boundaryIntersection_mem w C) j,
        ite_eq_left hj, pow_one (f d.val)]
      exact p.asIdeal.mul_mem_right _ hn
    refine ⟨S.map Function.Embedding.some, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨S, hS, ?_⟩
      rw [MonomialSchedule.Construction.boundaryFaceBranches, ite_eq_right hCS]
      exact List.mem_singleton_self _
    · intro j hj
      cases j with
      | none => exact False.elim (hn hj)
      | some j => exact Finset.mem_map.mpr ⟨j, hsome j hj, rfl⟩

theorem boundarySchedule_controlledTransform {R : Type u} [CommRing R]
    {ι : Type u} [Fintype ι] [DecidableEq ι] (w : ι → R) (a : ι → ℕ)
    (b : ℕ) (C : Finset ι) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C) (i : C) :
    ControlledTransform.Construction.blowupControlledTransform (CountReduction.Construction.boundaryIntersectionIdeal w C)
      (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}) b (boundaryIntersectionGenerator w C i) =
      Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement
        (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (CountReduction.Construction.boundaryIntersectionIdeal w C) (boundaryIntersectionGenerator w C i)
          C w (boundaryIntersection_mem w C)) (MonomialSchedule.Construction.boundaryScheduleExponents a b C)} := by
  exact LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement_controlledTransform _ _ C w (boundaryIntersection_mem w C) a b hC.2.1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Schedule.Construction

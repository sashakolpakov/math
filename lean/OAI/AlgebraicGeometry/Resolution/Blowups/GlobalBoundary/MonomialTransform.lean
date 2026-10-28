import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.ChosenGlobalReesCover

/-! # Monomial Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.MonomialTransform.Construction

noncomputable section

/-! Native global permissibility and exact monomial transformation along the common chosen centers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem finite_ideal_monomial_le_intersection_power
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (D : ι → Ideal R) (a : ι → ℕ) (C : Finset ι) (b : ℕ)
    (hb : b ≤ ∑ j ∈ C, a j) : (∏ j, D j ^ a j) ≤ C.sup D ^ b := by
  classical
  have hsplit : (∏ j, D j ^ a j) =
      (∏ j ∈ C, D j ^ a j) * ∏ j ∈ Finset.univ \ C, D j ^ a j :=
    (Finset.prod_mul_prod_compl C (fun j => D j ^ a j)).symm
  rw [hsplit]
  apply Ideal.mul_le_left.trans
  apply le_trans _ (Ideal.pow_le_pow_right hb)
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun j hj => pow_le_pow_left' (Finset.le_sup (f := D) hj) (a j))

theorem boundaryMonomialSheaf_permissible {X : Scheme.{u}} {ι : Type v} [Fintype ι]
    (D : ι → X.IdealSheafData) (a : ι → ℕ) (C : Finset ι) (b : ℕ)
    (hb : b ≤ Boundary.MonomialSchedule.Construction.boundaryFaceWeight a C) :
    Global.MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ Intersection.Construction.boundaryIntersectionSheaf D C ^ b := by
  intro U
  rw [Global.MixedBoundary.Construction.boundaryMonomialSheaf_ideal]
  change (∏ j, (D j).ideal U ^ a j) ≤ ((Intersection.Construction.boundaryIntersectionSheaf D C).ideal U) ^ b
  rw [Intersection.Construction.boundaryIntersectionSheaf_ideal]
  exact finite_ideal_monomial_le_intersection_power (fun j => (D j).ideal U) a C b hb

theorem boundaryIntersectionSheaf_ne_bot {X : Scheme.{u}} {ι : Type v}
    (D : ι → X.IdealSheafData) (C : Finset ι) (hC : C.Nonempty) (hD : ∀ j, D j ≠ ⊥) :
    Intersection.Construction.boundaryIntersectionSheaf D C ≠ ⊥ := by
  obtain ⟨j, hj⟩ := hC
  intro he
  have hle : D j ≤ Intersection.Construction.boundaryIntersectionSheaf D C := Finset.le_sup hj
  rw [he] at hle
  exact hD j (le_bot_iff.mp hle)

theorem global_boundary_monomial_transform
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) {β : Type u} [Fintype β]
    (D : β → X.IdealSheafData) (C : Finset β) (a : β → ℕ) (b : ℕ)
    (hb : b ≤ Boundary.MonomialSchedule.Construction.boundaryFaceWeight a C)
    {ι : Type u} (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).1 = ⊤)
    (κ : ι → Type u) (g : ∀ i, κ i → I.ideal (U i))
    (hgen : ∀ i, Ideal.span (Set.range (fun j => (g i j).val)) = I.ideal (U i))
    (w : ∀ i, β → Γ(X, U i)) (hD : ∀ i j, (D j).ideal (U i) = Ideal.span {w i j})
    (hw : ∀ i j, j ∈ C → w i j ∈ I.ideal (U i)) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI b =
      Global.MixedBoundary.Construction.boundaryMonomialSheaf (Global.MixedBoundary.Construction.globalBlowupMixedBoundary I hI D C) (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a b C) := by
  apply ChosenGlobalReesCover.Construction.idealSheaf_eq_of_chosen_globalReesCharts I hI U hcover κ g hgen
  intro i j
  exact Global.MixedBoundary.Construction.global_boundary_monomial_transform_on_chart I hI D C a b hb (U i) (w i) (hD i) (hw i) (g i j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.MonomialTransform.Construction

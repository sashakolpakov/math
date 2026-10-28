import OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentedRelative
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence

/-! # Relative Divided -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.RelativeDivided.RelativeDividedQuotient

noncomputable section

/-!
# Relative free divided powers under coefficient quotients

Given a surjective PD map from an embedded characteristic-zero base,
the full relative divided-power ideal descends through the coefficient
kernel. Its quotient is identified with the actual free divided-power
algebra on the target coefficients. Both the target base divided powers
and the coordinate operations are preserved.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (S R σ K : Type u) [CommRing S] [CommRing R] [Algebra S R]
  [Field K] [CharZero K] [Algebra S K]
  (h : Function.Injective (algebraMap S K))
  (hs : Function.Surjective (algebraMap S R))
  (IS : Ideal S) (δS : DividedPowers IS) (IR : Ideal R) (δR : DividedPowers IR)
  (hφ : DividedPowers.IsDPMorphism δS δR (algebraMap S R))
  (hI : IS.map (algebraMap S R) = IR)

local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "L" => RingHom.ker (algebraMap S R)
local notation "JS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal S σ IS
local notation "JR" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ IR
local notation "γS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralPowers.MultivariableGeneralPowers.dividedPowers S σ K h IS δS
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.Ring S R σ hs
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotient S R σ hs
local notation "eΓ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.algebraEquiv S R σ K h hs

theorem ideal_eq_comap : JS = IS.comap (Multivariable.Reduction.MultivariableReduction.augmentation S σ).toRingHom := by
  rw [← Multivariable.Reduction.MultivariableReduction.reduction_kernel]
  ext a
  change (Ideal.Quotient.mk IS (Multivariable.Reduction.MultivariableReduction.augmentation S σ a) = 0) ↔
    Multivariable.Reduction.MultivariableReduction.augmentation S σ a ∈ IS
  exact Ideal.Quotient.eq_zero_iff_mem

include hφ in
theorem quotient_compatible :
    DividedPowers.IsSubDPIdeal γS ((L).map (algebraMap S GS) ⊓ JS) :=
  AugmentedRelative.AugmentedRelativeQuotient.isSubDPIdeal S GS (Multivariable.Reduction.MultivariableReduction.augmentation S σ)
    IS δS JS γS (ideal_eq_comap S σ IS)
    (Multivariable.GeneralPowers.MultivariableGeneralPowers.base_isDPMorphism S σ K h IS δS) L
    (DividedPowers.isSubDPIdeal_ker δS δR hφ)

def quotientIdeal : Ideal Q := (JS).map (q).toRingHom

def quotientPowers : DividedPowers (quotientIdeal S R σ hs IS) :=
  DividedPowers.Quotient.dividedPowers γS (quotient_compatible S R σ K h IS δS IR δR hφ)

theorem quotient_isDPMorphism :
    DividedPowers.IsDPMorphism γS (quotientPowers S R σ K h hs IS δS IR δR hφ) (q).toRingHom :=
  DividedPowers.Quotient.isDPMorphism γS (quotient_compatible S R σ K h IS δS IR δR hφ)

include hs hI in
theorem baseChange_ideal_map : (JS).map (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ).toRingHom = JR := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with ⟨a, rfl⟩ | ⟨⟨m, i⟩, rfl⟩
    · change Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ (algebraMap S GS a) ∈ JR
      rw [Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_coefficient]
      have hm : algebraMap S R a ∈ IR := hI ▸ Ideal.mem_map_of_mem _ a.property
      exact Ideal.subset_span (Or.inl ⟨⟨_, hm⟩, rfl⟩)
    · change Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ (m + 1) i) ∈ JR
      rw [Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator]
      exact Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ IR i _ (Nat.succ_ne_zero m)
  · apply Ideal.span_le.mpr
    intro a ha
    rcases ha with ⟨a, rfl⟩ | ⟨⟨m, i⟩, rfl⟩
    · have ha : (a : R) ∈ IS.map (algebraMap S R) := hI.symm ▸ a.property
      obtain ⟨s, hsI, hsA⟩ := (Ideal.mem_map_iff_of_surjective (algebraMap S R) hs).mp ha
      have hm := Ideal.mem_map_of_mem (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ).toRingHom
        (show algebraMap S GS s ∈ JS from Ideal.subset_span (Or.inl ⟨⟨s, hsI⟩, rfl⟩))
      change Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ (algebraMap S GS s) ∈ _ at hm
      rw [Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_coefficient, hsA] at hm
      exact hm
    · have hm := Ideal.mem_map_of_mem (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ).toRingHom
        (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem S σ IS i (m + 1) (Nat.succ_ne_zero m))
      change Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ (m + 1) i) ∈ _ at hm
      rw [Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator] at hm
      exact hm

include hI in
theorem ideal_map : (quotientIdeal S R σ hs IS).map (eΓ).symm.toRingHom = JR := by
  change ((JS).map (q).toRingHom).map (eΓ).symm.toRingHom = JR
  rw [Ideal.map_map]
  exact baseChange_ideal_map S R σ hs IS IR hI

/-- Full relative divided powers on the actual target free algebra. -/
def dividedPowers : DividedPowers JR :=
  DividedPowers.ofRingEquiv (e := (eΓ).symm.toRingEquiv) (ideal_map S R σ K h hs IS IR hI)
    (quotientPowers S R σ K h hs IS δS IR δR hφ)

theorem equiv_symm_isDPMorphism :
    DividedPowers.IsDPMorphism (quotientPowers S R σ K h hs IS δS IR δR hφ)
      (RelativeDividedQuotient.dividedPowers S R σ K h hs IS δS IR δR hφ hI) (eΓ).symm.toRingHom where
  ideal_comp := (ideal_map S R σ K h hs IS IR hI).le
  dpow_comp a _ := by
    change (eΓ).symm ((quotientPowers S R σ K h hs IS δS IR δR hφ).dpow _
      ((eΓ) ((eΓ).symm a))) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl

theorem baseChange_isDPMorphism :
    DividedPowers.IsDPMorphism γS (RelativeDividedQuotient.dividedPowers S R σ K h hs IS δS IR δR hφ hI)
      (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ).toRingHom :=
  (equiv_symm_isDPMorphism S R σ K h hs IS δS IR δR hφ hI).comp _
    (quotient_isDPMorphism S R σ K h hs IS δS IR δR hφ)

theorem coordinate_dpow (n : ℕ) (i : σ) :
    (RelativeDividedQuotient.dividedPowers S R σ K h hs IS δS IR δR hφ hI).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) =
      Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i := by
  have hd := (baseChange_isDPMorphism S R σ K h hs IS δS IR δR hφ hI).dpow_comp
    (n := n) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i) (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem S σ IS i 1 one_ne_zero)
  change (RelativeDividedQuotient.dividedPowers S R σ K h hs IS δS IR δR hφ hI).dpow n
    (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i)) =
      Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ ((γS).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i)) at hd
  rw [Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator, Multivariable.GeneralPowers.MultivariableGeneralPowers.coordinate_dpow,
    Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator] at hd
  exact hd

theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism δR (RelativeDividedQuotient.dividedPowers S R σ K h hs IS δS IR δR hφ hI)
      (algebraMap R GR) := by
  apply DividedPowers.IsDPMorphism.of_comp δS δR
    (RelativeDividedQuotient.dividedPowers S R σ K h hs IS δS IR δR hφ hI)
    (algebraMap S R) (algebraMap R GR) hI.symm hφ
  have hd := (baseChange_isDPMorphism S R σ K h hs IS δS IR δR hφ hI).comp _
    (Multivariable.GeneralPowers.MultivariableGeneralPowers.base_isDPMorphism S σ K h IS δS)
  have he : (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ).toRingHom.comp (algebraMap S GS) =
      (algebraMap R GR).comp (algebraMap S R) := by
    ext s
    exact Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_coefficient S R σ s
  rw [he] at hd
  exact hd

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.RelativeDivided.RelativeDividedQuotient

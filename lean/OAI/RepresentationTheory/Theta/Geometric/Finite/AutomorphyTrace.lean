import OAI.RepresentationTheory.Theta.Geometric.AutomorphySections
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Automorphy Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Finite lattice traces descend sections from an intermediate period cover. -/

open scoped BigOperators ContDiff

variable {Φ : Torus.Data.CM.ProjectivePeriodData} (J : Φ.AutomorphyFactor)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.value_ne_zero (l : Φ.periodIntegerLattice) (z : Φ.space) : J.value l z ≠ 0 := by
  have h := J.add (-l) l z
  rw [neg_add_cancel, J.zero] at h
  intro hz
  rw [hz, mul_zero] at h
  exact one_ne_zero h

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.translateSection (l : Φ.periodIntegerLattice) (t : Φ.space → ℂ) (z : Φ.space) : ℂ :=
  t (z + l.val) / J.value l z

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.translateSection_zero (t : Φ.space → ℂ) : J.translateSection 0 t = t := by
  funext z
  simp only [Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.translateSection, ZeroMemClass.coe_zero, add_zero, J.zero, div_one]

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.translateSection_add (l m : Φ.periodIntegerLattice) (t : Φ.space → ℂ) :
    J.translateSection (l + m) t = J.translateSection l (J.translateSection m t) := by
  funext z
  change t (z + (l.val + m.val)) / J.value (l + m) z =
    (t ((z + l.val) + m.val) / J.value m (z + l.val)) / J.value l z
  rw [add_comm l m, J.add, div_div, add_assoc]

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.translateSection_eq_of_sub_mem (Γ : AddSubgroup Φ.periodIntegerLattice)
    (t : Φ.space → ℂ) (ht : ∀ l ∈ Γ, J.translateSection l t = t)
    (l m : Φ.periodIntegerLattice) (hlm : l - m ∈ Γ) :
    J.translateSection l t = J.translateSection m t := by
  have he : m + (l - m) = l := by abel
  rw [← he, J.translateSection_add, ht (l - m) hlm]

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.cosetSection (Γ : AddSubgroup Φ.periodIntegerLattice) (t : Φ.space → ℂ)
    (ht : ∀ l ∈ Γ, J.translateSection l t = t) :
    Φ.periodIntegerLattice ⧸ Γ → Φ.space → ℂ :=
  Quotient.lift (fun l => J.translateSection l t) (by
    intro l m h
    exact J.translateSection_eq_of_sub_mem Γ t ht l m
      (QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.sound h)))

@[simp]
theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.cosetSection_mk (Γ : AddSubgroup Φ.periodIntegerLattice) (t : Φ.space → ℂ)
    (ht : ∀ l ∈ Γ, J.translateSection l t = t) (l : Φ.periodIntegerLattice) :
    J.cosetSection Γ t ht (QuotientAddGroup.mk l) = J.translateSection l t := rfl

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.finiteTrace (Γ : AddSubgroup Φ.periodIntegerLattice) [Fintype (Φ.periodIntegerLattice ⧸ Γ)]
    (t : Φ.space → ℂ) (ht : ∀ l ∈ Γ, J.translateSection l t = t) (z : Φ.space) : ℂ :=
  ∑ c : Φ.periodIntegerLattice ⧸ Γ, J.cosetSection Γ t ht c z

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.finiteTrace_translates (Γ : AddSubgroup Φ.periodIntegerLattice)
    [Fintype (Φ.periodIntegerLattice ⧸ Γ)] (t : Φ.space → ℂ)
    (ht : ∀ l ∈ Γ, J.translateSection l t = t)
    (l : Φ.periodIntegerLattice) (z : Φ.space) :
    J.finiteTrace Γ t ht (z + l.val) = J.value l z * J.finiteTrace Γ t ht z := by
  have hshift (c : Φ.periodIntegerLattice ⧸ Γ) :
      J.cosetSection Γ t ht c (z + l.val) =
        J.value l z * J.cosetSection Γ t ht (QuotientAddGroup.mk l + c) z := by
    obtain ⟨m, rfl⟩ := QuotientAddGroup.mk_surjective c
    rw [← QuotientAddGroup.mk_add, J.cosetSection_mk, J.cosetSection_mk,
      J.translateSection_add]
    simp only [Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.translateSection]
    field_simp [J.value_ne_zero l z]
  simp_rw [Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.finiteTrace, hshift]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk l : Φ.periodIntegerLattice ⧸ Γ))
    (fun c => J.cosetSection Γ t ht c z)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.translateSection_contDiff (hJ : ∀ l, ContDiff ℂ ∞ (J.value l))
    (l : Φ.periodIntegerLattice) (t : Φ.space → ℂ) (ht : ContDiff ℂ ∞ t) :
    ContDiff ℂ ∞ (J.translateSection l t) :=
  (ht.comp (contDiff_id.add contDiff_const)).div (hJ l) (J.value_ne_zero l)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.finiteTrace_contDiff (hJ : ∀ l, ContDiff ℂ ∞ (J.value l))
    (Γ : AddSubgroup Φ.periodIntegerLattice) [Fintype (Φ.periodIntegerLattice ⧸ Γ)]
    (t : Φ.space → ℂ) (ht : ∀ l ∈ Γ, J.translateSection l t = t)
    (hreg : ContDiff ℂ ∞ t) : ContDiff ℂ ∞ (J.finiteTrace Γ t ht) := by
  apply ContDiff.sum
  intro c _
  obtain ⟨l, rfl⟩ := QuotientAddGroup.mk_surjective c
  exact J.translateSection_contDiff hJ l t hreg

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.finiteTrace_eq_of_vanish (Γ : AddSubgroup Φ.periodIntegerLattice)
    [Fintype (Φ.periodIntegerLattice ⧸ Γ)] (t : Φ.space → ℂ)
    (ht : ∀ l ∈ Γ, J.translateSection l t = t) (z : Φ.space)
    (hvanish : ∀ l : Φ.periodIntegerLattice,
      (QuotientAddGroup.mk l : Φ.periodIntegerLattice ⧸ Γ) ≠ 0 → t (z + l.val) = 0) :
    J.finiteTrace Γ t ht z = t z := by
  classical
  unfold Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.finiteTrace
  rw [Finset.sum_eq_single (0 : Φ.periodIntegerLattice ⧸ Γ)]
  · change J.translateSection 0 t z = t z
    rw [J.translateSection_zero]
  · intro c _ hc
    obtain ⟨l, rfl⟩ := QuotientAddGroup.mk_surjective c
    change t (z + l.val) / J.value l z = 0
    rw [hvanish l hc, zero_div]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

end

/-! Compactness turns pointwise automorphic generators into one finite family. -/

open scoped ContDiff

variable {Φ : Torus.Data.CM.ProjectivePeriodData} (J : Φ.AutomorphyFactor)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.nonzero_of_same_period (t : Φ.space → ℂ)
    (ht : ∀ (l : Φ.periodIntegerLattice) z, t (z + l.val) = J.value l z * t z)
    (p q : Φ.space) (hp : t p ≠ 0)
    (hpq : (QuotientAddGroup.mk p : Φ.periodTorus) = QuotientAddGroup.mk q) : t q ≠ 0 := by
  let l : Φ.periodIntegerLattice := ⟨q - p, QuotientAddGroup.eq_iff_sub_mem.mp hpq.symm⟩
  have h := ht l p
  have harg : p + l.val = q := by dsimp [l]; abel
  rw [harg] at h
  rw [h]
  exact mul_ne_zero (J.value_ne_zero l p) hp

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.exists_finite_generators
    (h : ∀ p : Φ.space, ∃ t : Φ.space → ℂ, ContDiff ℂ ∞ t ∧ t p ≠ 0 ∧
      ∀ (l : Φ.periodIntegerLattice) z, t (z + l.val) = J.value l z * t z) :
    ∃ F : Finset (Φ.space → ℂ),
      (∀ t ∈ F, ContDiff ℂ ∞ t) ∧
      (∀ t ∈ F, ∀ (l : Φ.periodIntegerLattice) z, t (z + l.val) = J.value l z * t z) ∧
      ∀ p : Φ.space, ∃ t ∈ F, t p ≠ 0 := by
  classical
  choose t hreg hnonzero htrans using h
  let U (p : Φ.space) : Set Φ.periodTorus := QuotientAddGroup.mk '' {z | t p z ≠ 0}
  have hU (p) : IsOpen (U p) := QuotientAddGroup.isOpenMap_coe _
    (isOpen_ne_fun (hreg p).continuous continuous_const)
  have hcover : (Set.univ : Set Φ.periodTorus) ⊆ ⋃ p, U p := by
    intro q _
    obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact Set.mem_iUnion.mpr ⟨p, p, hnonzero p, rfl⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨S.image t, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    exact hreg p
  · intro a ha
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    exact htrans p
  · intro p
    obtain ⟨a, ha, z, hz, he⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ (QuotientAddGroup.mk p)))
    exact ⟨t a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      J.nonzero_of_same_period (t a) (htrans a) z p hz he⟩

end

end OAI.RepresentationTheory.Theta.Geometric

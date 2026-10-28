import OAI.RepresentationTheory.Theta.Geometric.Data

/-! # Joint Local Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The completed reference lattice is stable under every split integral
coordinate multiplier. This follows from its original integral CM action
and the supplied bijective integral completion map. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.jointLocalEmbedding (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : Fin s × Bool → Fin 3 → ℚ_[q] :=
  fun v i => D.localEmbedding v (x i)

def Data.ActiveHeckeThetaData.jointLocalLattice : Submodule ℤ_[q] (Fin s × Bool → Fin 3 → ℚ_[q]) :=
  Submodule.span ℤ_[q] (D.jointLocalEmbedding '' (D.pel.reference.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)))

def Data.ActiveHeckeThetaData.jointLocalScale (c : Fin s × Bool → ℤ_[q]) :
    (Fin s × Bool → Fin 3 → ℚ_[q]) →ₗ[ℤ_[q]] (Fin s × Bool → Fin 3 → ℚ_[q]) where
  toFun u v := c v • u v
  map_add' u w := by
    ext v i
    change c v • (u v i + w v i) = c v • u v i + c v • w v i
    exact smul_add _ _ _
  map_smul' a u := by
    ext v i
    change c v • (a • u v i) = a • (c v • u v i)
    exact smul_comm _ _ _

theorem Data.ActiveHeckeThetaData.jointLocalEmbedding_integer (hc : D.HasFiniteCoordinates)
    (a : NumberField.RingOfIntegers E) (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    D.jointLocalEmbedding ((a : E) • x) =
      Data.ActiveHeckeThetaData.jointLocalScale (fun v => D.pel.localCharacter v a) (D.jointLocalEmbedding x) := by
  funext v i
  change D.localEmbedding v ((a : E) * x i) =
    (D.pel.localCharacter v a : ℚ_[q]) * D.localEmbedding v (x i)
  rw [map_mul, hc.1]

theorem Data.ActiveHeckeThetaData.jointLocalScale_integer_mem (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (a : NumberField.RingOfIntegers E) (u : Fin s × Bool → Fin 3 → ℚ_[q])
    (hu : u ∈ D.jointLocalLattice) :
    Data.ActiveHeckeThetaData.jointLocalScale (fun v => D.pel.localCharacter v a) u ∈ D.jointLocalLattice := by
  have hstable : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice D.pel.reference.lattice := by
    rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    rw [← D.jointLocalEmbedding_integer hc]
    exact Submodule.subset_span ⟨_, hstable.2.2 a x hx, rfl⟩
  | zero =>
    rw [map_zero]
    exact D.jointLocalLattice.zero_mem
  | add u w _ _ hu hw =>
    rw [map_add]
    exact D.jointLocalLattice.add_mem hu hw
  | smul c u _ hu =>
    rw [map_smul]
    exact D.jointLocalLattice.smul_mem c hu

theorem Data.ActiveHeckeThetaData.jointLocalScale_completed_mem (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (t : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E)
    (u : Fin s × Bool → Fin 3 → ℚ_[q]) (hu : u ∈ D.jointLocalLattice) :
    Data.ActiveHeckeThetaData.jointLocalScale (D.pel.localCompletionMap t) u ∈ D.jointLocalLattice := by
  induction t using TensorProduct.inductionOn with
  | tmul z a =>
    have he : Data.ActiveHeckeThetaData.jointLocalScale (D.pel.localCompletionMap (z ⊗ₜ[ℤ] a)) u =
        z • Data.ActiveHeckeThetaData.jointLocalScale (fun v => D.pel.localCharacter v a) u := by
      ext v i
      change (z * D.pel.localCharacter v a) • u v i = z • (D.pel.localCharacter v a • u v i)
      exact mul_smul _ _ _
    rw [he]
    exact D.jointLocalLattice.smul_mem z (D.jointLocalScale_integer_mem hg hc a u hu)
  | add t w ht hw =>
    have he : Data.ActiveHeckeThetaData.jointLocalScale (D.pel.localCompletionMap (t + w)) u =
        Data.ActiveHeckeThetaData.jointLocalScale (D.pel.localCompletionMap t) u + Data.ActiveHeckeThetaData.jointLocalScale (D.pel.localCompletionMap w) u := by
      ext v i
      change (D.pel.localCompletionMap (t + w) v) • u v i = _
      rw [map_add, Pi.add_apply, add_smul]
      rfl
    rw [he]
    exact D.jointLocalLattice.add_mem ht hw

theorem Data.ActiveHeckeThetaData.jointLocalScale_mem (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (c : Fin s × Bool → ℤ_[q])
    (u : Fin s × Bool → Fin 3 → ℚ_[q]) (hu : u ∈ D.jointLocalLattice) :
    Data.ActiveHeckeThetaData.jointLocalScale c u ∈ D.jointLocalLattice := by
  obtain ⟨t, rfl⟩ := hgood.1.2 c
  exact D.jointLocalScale_completed_mem hg hc t u hu

end

end OAI.RepresentationTheory.Theta.Geometric

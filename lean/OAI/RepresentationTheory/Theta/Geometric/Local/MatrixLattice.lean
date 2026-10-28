import OAI.RepresentationTheory.Theta.Geometric.Local.IntegralDetection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates

/-! # Matrix Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Integral local matrices act on the literal standard coordinate
lattices. Combining every local place with the away condition recovers
preservation of the original integral reference lattice. -/

theorem Local.MatrixLattice.standardLocalLattice_mem_iff (q : ℕ) [Fact q.Prime] (u : Fin 3 → ℚ_[q]) :
    u ∈ Data.ActiveHeckeThetaData.standardLocalLattice (q := q) ↔ ∀ i, ‖u i‖ ≤ 1 := by
  have hb : (Pi.basisFun ℚ_[q] (Fin 3) : Fin 3 → Fin 3 → ℚ_[q]) =
      fun i => Pi.single i 1 := funext (Pi.basisFun_apply ℚ_[q] (Fin 3))
  change u ∈ Submodule.span ℤ_[q] (Set.range fun i => Pi.single i (1 : ℚ_[q])) ↔ _
  rw [← hb, (Pi.basisFun ℚ_[q] (Fin 3)).mem_span_iff_repr_mem ℤ_[q]]
  constructor
  · intro h i
    obtain ⟨a, ha⟩ := h i
    have he : (a : ℚ_[q]) = u i := by simpa using ha
    rw [← he]
    exact a.property
  · intro h i
    exact ⟨⟨u i, h i⟩, by simp; rfl⟩

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.localMatrix_reference_action (g : D.RationalSU) (v : Fin s × Bool) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (D.localMatrix v g).val.mulVec (fun i => D.localEmbedding v (u i)) =
      fun i => D.localEmbedding v (D.rationalLinear g u i) := by
  symm
  funext i
  exact RingHom.map_mulVec (D.localEmbedding v) g.val.val u i

theorem Data.ActiveHeckeThetaData.localMatrix_integral_reference (hc : D.HasFiniteCoordinates)
    (g : D.RationalSU) (v : Fin s × Bool) (hg : D.localMatrix v g ∈ SphericalGU.Spherical.integralSL3 q)
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hu : u ∈ D.pel.reference.lattice) :
    (fun i => D.localEmbedding v (D.rationalLinear g u i)) ∈ Data.ActiveHeckeThetaData.standardLocalLattice (q := q) := by
  rw [← D.localMatrix_reference_action, Local.MatrixLattice.standardLocalLattice_mem_iff]
  apply AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport.integralSL3_mulVec_integral q _ hg
  apply (Local.MatrixLattice.standardLocalLattice_mem_iff q _).mp
  rw [← hc.2.1 v]
  exact Submodule.subset_span ⟨u, hu, rfl⟩

theorem Data.ActiveHeckeThetaData.rationalLinear_integral_of_all_local (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (g : D.RationalSU)
    (hloc : ∀ v, D.localMatrix v g ∈ SphericalGU.Spherical.integralSL3 q)
    (haway : D.away g ∈ D.awayLevel) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hu : u ∈ D.pel.reference.lattice) :
    D.rationalLinear g u ∈ D.pel.reference.lattice := by
  apply D.referenceLattice_of_local_and_away hg hc hgood hdegree
  · intro v
    exact D.localMatrix_integral_reference hc g v (hloc v) u hu
  · exact (D.mem_awayLattice_iff _).mpr (D.away_level_clears_vector hc g haway ⟨u, hu⟩)

theorem Data.ActiveHeckeThetaData.rationalLinear_preserves_lattice_of_all_local (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (g : D.RationalSU)
    (hloc : ∀ v, D.localMatrix v g ∈ SphericalGU.Spherical.integralSL3 q)
    (haway : D.away g ∈ D.awayLevel) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    u ∈ D.pel.reference.lattice ↔ D.rationalLinear g u ∈ D.pel.reference.lattice := by
  constructor
  · exact D.rationalLinear_integral_of_all_local hg hc hgood hdegree g hloc haway u
  · intro hu
    have hloc' (v) : D.localMatrix v g⁻¹ ∈ SphericalGU.Spherical.integralSL3 q := by
      rw [map_inv]
      exact (SphericalGU.Spherical.integralSL3 q).inv_mem (hloc v)
    have haway' : D.away g⁻¹ ∈ D.awayLevel := by
      rw [map_inv]
      exact D.awayLevel.inv_mem haway
    have h := D.rationalLinear_integral_of_all_local hg hc hgood hdegree g⁻¹ hloc' haway'
      (D.rationalLinear g u) hu
    rw [map_inv] at h
    change (D.rationalLinear g).symm (D.rationalLinear g u) ∈ _ at h
    rwa [LinearEquiv.symm_apply_apply] at h

end

end OAI.RepresentationTheory.Theta.Geometric

import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.LatticeTopology
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
import OAI.RepresentationTheory.Theta.AdelicTopology

/-! # Rational Lattice Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalLatticeTopology.TestTransport

noncomputable section

/-! The corresponding integer-lattice neighborhood basis for PoissonAutomorphy's
original rational finite-adele coordinates. -/

open scoped Classical _root_.Topology

theorem rationalFiniteAdeles_totallyDisconnected : TotallyDisconnectedSpace RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := by
  have hc : Continuous (fun x : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => fun v => x v) := RestrictedProduct.continuous_coe
  exact ⟨isTotallyDisconnected_of_image hc.continuousOn DFunLike.coe_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem rationalPosition_integer_lattice_nhds {I : Type*} [Fintype I]
    (U : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hU : U ∈ 𝓝 (0 : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) :
    ∃ N : ℕ, ∃ hN : 0 < N,
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) (N : ℚ) (by exact_mod_cast hN.ne') : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) ⊆ U := by
  let := rationalFiniteAdeles_totallyDisconnected
  obtain ⟨V, hVU⟩ := Finite.LatticeTopology.TestTransport.open_add_subgroup_inside_nhds_zero U hU
  let : CompactSpace (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I)).toAddSubgroup :=
    isCompact_iff_compactSpace.mp RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isCompact
  let W := V.comap (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I)).toAddSubgroup.subtype continuous_subtype_val
  obtain ⟨N, hN, hsmall⟩ := RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.compact_openAddSubgroup_integer_multiple W
  refine ⟨N, hN, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  apply hVU
  change RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (N : ℚ) y ∈ V
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_natCast]
  exact hsmall ⟨y, hy⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalLatticeTopology.TestTransport

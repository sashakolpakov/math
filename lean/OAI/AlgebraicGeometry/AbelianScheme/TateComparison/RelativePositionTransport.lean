import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeTransport

/-! # Relative Position Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionTransport

noncomputable section

/-! Linear coordinate changes preserve full lattices and their actual
simultaneous-basis relative positions. -/

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

def rankThreeLatticeEquiv (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :
    Duality.RankThreeLattice R K ≃ Duality.RankThreeLattice R K :=
  (Submodule.orderIsoMapComap (e.restrictScalars R)).toEquiv.subtypeEquiv fun L => by
    constructor
    · intro h
      have : Submodule.IsLattice K L := h
      exact LatticeTransport.isLattice_map_surjective L e.toLinearMap e.surjective
    · intro h
      have : Submodule.IsLattice K (L.map (e.toLinearMap.restrictScalars R)) := h
      have hL := LatticeTransport.isLattice_comap_equiv (L.map (e.toLinearMap.restrictScalars R)) e
      rw [Submodule.comap_map_eq_of_injective
        (f := e.toLinearMap.restrictScalars R) e.injective] at hL
      exact hL

theorem rankThreeLatticeEquiv_val (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (L : Duality.RankThreeLattice R K) :
    (rankThreeLatticeEquiv e L).val = L.val.map (e.toLinearMap.restrictScalars R) := rfl

theorem map_basis_span (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (b : Module.Basis (Fin 3) K (Fin 3 → K)) :
    (Submodule.span R (Set.range b)).map (e.toLinearMap.restrictScalars R) =
      Submodule.span R (Set.range (b.map e)) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem map_scaled_basis_span (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (b : Module.Basis (Fin 3) K (Fin 3 → K)) (c : Fin 3 → K) :
    (Submodule.span R (Set.range fun i => c i • b i)).map (e.toLinearMap.restrictScalars R) =
      Submodule.span R (Set.range fun i => c i • (b.map e) i) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact e.map_smul (c i) (b i)

theorem relativePosition_map (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (π : R) (a : Fin 3 → ℤ) (L M : Duality.RankThreeLattice R K)
    (h : Duality.RelativePosition π a L M) :
    Duality.RelativePosition π a (rankThreeLatticeEquiv e L) (rankThreeLatticeEquiv e M) := by
  obtain ⟨b, hL, hM⟩ := h
  refine ⟨b.map e, ?_, ?_⟩
  · rw [rankThreeLatticeEquiv_val, hL, map_basis_span]
  · rw [rankThreeLatticeEquiv_val, hM, map_scaled_basis_span]

theorem rankThreeLatticeEquiv_symm_apply (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (L : Duality.RankThreeLattice R K) :
    rankThreeLatticeEquiv e.symm (rankThreeLatticeEquiv e L) = L := by
  apply Subtype.ext
  rw [rankThreeLatticeEquiv_val, rankThreeLatticeEquiv_val]
  change (L.val.map (e.restrictScalars R).toLinearMap).map
    (e.restrictScalars R).symm.toLinearMap = L.val
  rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm, Submodule.comap_map_eq_of_injective
    (e.restrictScalars R).injective]

theorem relativePosition_map_iff (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (π : R) (a : Fin 3 → ℤ) (L M : Duality.RankThreeLattice R K) :
    Duality.RelativePosition π a (rankThreeLatticeEquiv e L) (rankThreeLatticeEquiv e M) ↔
      Duality.RelativePosition π a L M := by
  constructor
  · intro h
    have h' := relativePosition_map e.symm π a _ _ h
    simpa only [rankThreeLatticeEquiv_symm_apply] using h'
  · exact relativePosition_map e π a L M

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionTransport

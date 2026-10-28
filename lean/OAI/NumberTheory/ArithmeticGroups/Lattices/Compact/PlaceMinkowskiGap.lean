import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.QuadraticInvariant
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantGap

/-! # Place Minkowski Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.PlaceMinkowskiGap.Construction

noncomputable section

/-! At a compact real place, the descended positive invariant form has
nonzero values in a discrete coefficient lattice. This bounds every
nonzero Minkowski lattice vector uniformly away from zero under the
full archimedean group action. -/

open scoped Classical _root_.NumberField
open _root_.Matrix _root_.NumberField _root_.NumberField.mixedEmbedding

theorem quadraticValue_standard_minkowski_mem
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) k) {x : Fin n → mixedSpace k}
    (hx : x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    QuadraticValue.Construction.quadraticValue (Q.map (mixedEmbedding k)) x ∈ IntegralLattice.Construction.scalarLatticeImage (QuadraticValue.Construction.quadraticCoefficientModule Q) := by
  obtain ⟨a, ha, rfl⟩ := hx
  have ha' : a ∈ Integral.Matrices.Construction.integralCoordinateLattice (R := 𝓞 k) n :=
    (Integral.Matrices.Construction.integralCoordinateLattice_eq_span (R := 𝓞 k) (k := k) n).symm ▸ ha
  have hi (i : Fin n) : ∃ b : 𝓞 k, (b : k) = a i := (Integral.Matrices.Construction.mem_integralCoordinateLattice a).mp ha' i
  choose b hb using hi
  have hab : a = fun i => (b i : k) := funext (fun i => (hb i).symm)
  subst a
  refine ⟨QuadraticValue.Construction.quadraticValue Q (fun i => (b i : k)), QuadraticValue.Construction.quadraticValue_integral_mem Q b, ?_⟩
  exact (QuadraticValue.Construction.quadraticValue_map (mixedEmbedding k) Q (fun i => (b i : k))).symm

theorem quadraticValue_standard_minkowski_ne_zero
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (v : k →+* ℝ) (Q : Matrix (Fin n) (Fin n) k)
    (hQ : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < QuadraticValue.Construction.quadraticValue (Q.map v) x)
    {x : Fin n → mixedSpace k} (hx : x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module)
    (hx0 : x ≠ 0) : QuadraticValue.Construction.quadraticValue (Q.map (mixedEmbedding k)) x ≠ 0 := by
  obtain ⟨a, _, rfl⟩ := hx
  have ha : a ≠ 0 := by
    intro h
    apply hx0
    rw [h, map_zero]
  change QuadraticValue.Construction.quadraticValue (Q.map (mixedEmbedding k)) (fun i => mixedEmbedding k (a i)) ≠ 0
  rw [QuadraticValue.Construction.quadraticValue_map]
  exact fun hz => QuadraticValue.Construction.quadraticValue_ne_zero_of_positive_real v Q hQ ha
    ((mixedEmbedding_injective k) (hz.trans (map_zero (mixedEmbedding k)).symm))

theorem compact_real_place_uniform_minkowski_gap
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (v : k →+* ℝ) (hv : Algebraic.IsCompactAtRealPlace G v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : G.matrixGroup.ArchimedeanProduct Set.univ,
      ∀ x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k G.dimension).module, x ≠ 0 →
        ε ≤ ‖Archimedean.Quotient.Construction.archimedeanRealRepresentation k G.dimension (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G.matrixGroup g).val x‖ := by
  obtain ⟨Q, hpos, hQ⟩ := Bilinear.InvariantIntegration.Construction.compact_real_place_positive_invariant_form G v hv
  let D := IntegralLattice.Construction.scalarLatticeImage (QuadraticValue.Construction.quadraticCoefficientModule Q)
  apply InvariantGap.Construction.uniform_gap_of_discrete_invariant
    (fun g x => Archimedean.Quotient.Construction.archimedeanRealRepresentation k G.dimension (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G.matrixGroup g).val x)
    (QuadraticValue.Construction.quadraticValue (Q.map (mixedEmbedding k))) (QuadraticValue.Construction.continuous_quadraticValue _) ?_
    (D : Set (mixedSpace k)) ?_ D.zero_mem
    (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k G.dimension).module : Set (Fin G.dimension → mixedSpace k))
  · intro x hx hx0
    exact ⟨quadraticValue_standard_minkowski_mem Q hx,
      quadraticValue_standard_minkowski_ne_zero v Q hpos hx hx0⟩
  · intro g x _
    exact Minkowski.QuadraticInvariant.Construction.minkowski_quadraticValue_invariant G.matrixGroup Q hQ g x
  · simp [QuadraticValue.Construction.quadraticValue]
  · exact isDiscrete_iff_discreteTopology.mpr
      (IntegralLattice.Construction.scalarLatticeImage_discrete _ (QuadraticValue.Construction.quadraticCoefficientModule_fg Q))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.PlaceMinkowskiGap.Construction

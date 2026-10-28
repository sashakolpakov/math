import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeStabilizers

/-! # Stabilizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.Stabilizer.Construction

noncomputable section

/-! Preserving the standard Minkowski lattice forces every matrix entry
to come from the ring of integers. Thus its stabilizer is exactly the
diagonal integral special-linear subgroup. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem vectorMixedEmbedding_coordinate_vector
    {k : Type} [Field k] {n : ℕ} (j : Fin n) :
    IntegralLattice.Construction.vectorMixedEmbedding (k := k) n (Pi.basisFun k (Fin n) j) =
      Pi.basisFun (mixedSpace k) (Fin n) j := by
  funext i
  simp [IntegralLattice.Construction.vectorMixedEmbedding, Pi.basisFun_apply, Pi.single_apply]

theorem minkowski_preserver_integral_columns
    {k : Type} [Field k] [NumberField k] {n : ℕ} (g : Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n)
    (hg : ∀ x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module,
      Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module)
    (j : Fin n) :
    ∃ a ∈ (IntegralLattice.FullLattice.standard k n).module,
      ∀ i, mixedEmbedding k (a i) = Archimedean.Quotient.Construction.archimedeanMixedSL k n g i j := by
  have hj : IntegralLattice.Construction.vectorMixedEmbedding (k := k) n (Pi.basisFun k (Fin n) j) ∈
      IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module :=
    ⟨Pi.basisFun k (Fin n) j, Submodule.subset_span (Set.mem_range_self j), rfl⟩
  obtain ⟨a, ha, he⟩ := hg _ hj
  refine ⟨a, ha, fun i => ?_⟩
  have hi := congrFun he i
  rw [vectorMixedEmbedding_coordinate_vector] at hi
  change mixedEmbedding k (a i) =
    (Archimedean.Quotient.Construction.archimedeanMixedSL k n g : Matrix (Fin n) (Fin n) (mixedSpace k)).mulVec
      (Pi.basisFun (mixedSpace k) (Fin n) j) i at hi
  simpa [Pi.basisFun_apply, Matrix.mulVec_single] using hi

theorem minkowski_preserver_is_integral
    {k : Type} [Field k] [NumberField k] {n : ℕ} (g : Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n)
    (hg : ∀ x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module,
      Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    g ∈ Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n := by
  choose a ha he using minkowski_preserver_integral_columns g hg
  let B : Matrix (Fin n) (Fin n) k := Matrix.of (fun i j => a j i)
  have hB : B.map (mixedEmbedding k) = (Archimedean.Quotient.Construction.archimedeanMixedSL k n g : Matrix (Fin n) (Fin n) (mixedSpace k)) := by
    ext i j : 1
    exact he j i
  have hdet : B.det = 1 := by
    apply mixedEmbedding_injective k
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hB, Matrix.SpecialLinearGroup.det_coe, map_one]
  let q : Algebraic.SL n k := ⟨B, hdet⟩
  have hq : Matrix.SpecialLinearGroup.map (mixedEmbedding k) q = Archimedean.Quotient.Construction.archimedeanMixedSL k n g :=
    Subtype.ext hB
  have hentry : ∀ i j, ∃ c : 𝓞 k, algebraMap (𝓞 k) k c = q i j := by
    intro i j
    have hj : a j ∈ Integral.Matrices.Construction.integralCoordinateLattice (R := 𝓞 k) n := by
      rw [Integral.Matrices.Construction.integralCoordinateLattice_eq_span]
      exact ha j
    exact (Integral.Matrices.Construction.mem_integralCoordinateLattice (a j)).mp hj i
  obtain ⟨A, hA⟩ := Integral.Matrices.Construction.specialLinear_lift_of_integral_entries q hentry
  refine ⟨A, ?_⟩
  change Archimedean.ExteriorAction.Construction.fullArchimedeanSLMap k n (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 k) k) A) = g
  rw [hA]
  apply Archimedean.Quotient.Construction.archimedeanMixedSL_injective k n
  rw [IntegralAction.Construction.archimedeanMixedSL_diagonal]
  exact hq

theorem fullArchimedeanIntegralSL_eq_minkowski_stabilizer
    {k : Type} [Field k] [NumberField k] {n : ℕ} :
    Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n =
      SubmoduleOrbit.Construction.submoduleImageStabilizer ((LatticeStabilizers.Construction.restrictScalarsAutomorphismHom (R := ℤ)).comp
        (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n))
        (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) := by
  ext g
  rw [StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff]
  constructor
  · intro hg x
    exact IntegralAction.Construction.integral_archimedean_preserves_minkowski_iff hg x
  · intro hg
    exact minkowski_preserver_is_integral g (fun x hx => (hg x).mpr hx)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.Stabilizer.Construction

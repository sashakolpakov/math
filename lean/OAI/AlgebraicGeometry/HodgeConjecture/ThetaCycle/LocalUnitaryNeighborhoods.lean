import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalCoefficientNeighborhoods
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixUnitNeighborhoods
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Local Unitary Neighborhoods -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods.CM

noncomputable section

/-! ThetaCycle: a local subgroup neighborhood contains matrix units whose
matrix and inverse differ from one by a single sufficiently divisible
integer times integral quadratic coefficients. -/

open scoped Classical _root_.NumberField _root_.Topology
open IsDedekindDomain

def quadraticMatrixPair {R I : Type*} [CommRing R] (d : R)
    (x : Fin 2 × I × I × Fin 2 → R) : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) × Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) :=
  (fun i j => ⟨x (0, i, j, 0), x (0, i, j, 1)⟩,
   fun i j => ⟨x (1, i, j, 0), x (1, i, j, 1)⟩)

theorem quadratic_matrix_pair_continuous {R I : Type*} [CommRing R] [TopologicalSpace R] (d : R) :
    Continuous (quadraticMatrixPair (I := I) d) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hx : Continuous (fun x : Fin 2 × I × I × Fin 2 → R =>
        (x (0, i, j, 0), x (0, i, j, 1))) := by fun_prop
    exact (RepresentationTheory.Theta.Adelic.SpecialUnitary.quadraticHomeomorph d).continuous_invFun.comp
      hx
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hx : Continuous (fun x : Fin 2 × I × I × Fin 2 → R =>
        (x (1, i, j, 0), x (1, i, j, 1))) := by fun_prop
    exact (RepresentationTheory.Theta.Adelic.SpecialUnitary.quadraticHomeomorph d).continuous_invFun.comp
      hx

theorem local_unitary_integer_neighborhood (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {I : Type*} [Fintype I] [DecidableEq I]
    (d : v.adicCompletion F) (G : Subgroup (Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (v.adicCompletion F) d))ˣ)
    (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ a : Fin 2 × I × I × Fin 2 → v.adicCompletion F,
      (∀ i, a i ∈ v.adicCompletionIntegers F) → ∀ g : G,
      (g.val.val - 1, (g⁻¹).val.val - 1) =
        quadraticMatrixPair d (fun i => algebraMap ℤ (v.adicCompletion F) n * a i) → g ∈ U := by
  obtain ⟨V, hV, hVU⟩ := MatrixUnitNeighborhoods.CM.matrix_unit_subgroup_zero_neighborhood G U hU
  have hzero : quadraticMatrixPair (I := I) d 0 = (0, 0) := by rfl
  have hpre : quadraticMatrixPair d ⁻¹' V ∈ 𝓝 (0 : Fin 2 × I × I × Fin 2 → v.adicCompletion F) :=
    (quadratic_matrix_pair_continuous d).continuousAt.preimage_mem_nhds (hzero.symm ▸ hV)
  obtain ⟨n, hn, hs⟩ := LocalCoefficientNeighborhoods.CM.local_integral_tuple_integer_multiple_small F v _ hpre
  refine ⟨n, hn, ?_⟩
  intro a ha g hg
  apply hVU g
  rw [hg]
  exact hs a ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods.CM

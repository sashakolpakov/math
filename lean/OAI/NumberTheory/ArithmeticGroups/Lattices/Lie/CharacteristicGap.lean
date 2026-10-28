import OAI.NumberTheory.ArithmeticGroups.Lattices.CharacteristicInvariant
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantGap

/-! # Characteristic Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.CharacteristicGap.Construction

noncomputable section

/-! Integral characteristic coefficients and anisotropy give a uniform
Minkowski norm bound for every conjugate of a nonzero integral Lie matrix. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem characteristicInvariant_integral_minkowski_mem
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (𝓞 k)) :
    CharacteristicInvariant.Construction.characteristicInvariant (A.map ((mixedEmbedding k).comp (algebraMap (𝓞 k) k))) ∈
      IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k (n + 1)).module := by
  rw [Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_eq_pi, CharacteristicInvariant.Construction.characteristicInvariant_map]
  intro i _
  exact ⟨CharacteristicInvariant.Construction.characteristicInvariant A i, rfl⟩

theorem anisotropic_characteristicInvariant_minkowski_ne_zero
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) (A : Matrix (Fin G.dimension) (Fin G.dimension) k)
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) (hA0 : A ≠ 0) :
    CharacteristicInvariant.Construction.characteristicInvariant (A.map (mixedEmbedding k)) ≠ 0 := by
  intro h
  apply CharacteristicInvariant.Construction.anisotropic_characteristicInvariant_ne_zero G haniso A hA hA0
  funext i
  apply mixedEmbedding_injective k
  have hi := congrFun h i
  rw [CharacteristicInvariant.Construction.characteristicInvariant_map] at hi
  simpa only [Pi.zero_apply, map_zero] using hi

def integralLieMixedSet
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k) :
    Set (Matrix (Fin G.dimension) (Fin G.dimension) (mixedSpace k)) :=
  {x | ∃ A : Matrix (Fin G.dimension) (Fin G.dimension) (𝓞 k),
    A.map (algebraMap (𝓞 k) k) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup ∧
      x = A.map ((mixedEmbedding k).comp (algebraMap (𝓞 k) k))}

theorem characteristicInvariant_integralLie_values
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G)
    (x : Matrix (Fin G.dimension) (Fin G.dimension) (mixedSpace k))
    (hx : x ∈ integralLieMixedSet G) (hx0 : x ≠ 0) :
    CharacteristicInvariant.Construction.characteristicInvariant x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k (G.dimension + 1)).module ∧
      CharacteristicInvariant.Construction.characteristicInvariant x ≠ 0 := by
  obtain ⟨A, hA, rfl⟩ := hx
  refine ⟨characteristicInvariant_integral_minkowski_mem A, ?_⟩
  have hne : A.map (algebraMap (𝓞 k) k) ≠ 0 := by
    intro h
    apply hx0
    change A.map ((mixedEmbedding k) ∘ (algebraMap (𝓞 k) k)) = 0
    rw [← Matrix.map_map, h]
    exact Matrix.map_zero _ (map_zero _)
  have h := anisotropic_characteristicInvariant_minkowski_ne_zero G haniso _ hA hne
  simpa only [Matrix.map_map, RingHom.coe_comp] using h

theorem anisotropic_integralLie_uniform_gap
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ g : Matrix.GeneralLinearGroup (Fin G.dimension) (mixedSpace k),
      ∀ x ∈ integralLieMixedSet G, x ≠ 0 → ε ≤ ‖g.val * x * (g⁻¹).val‖ := by
  let D := IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k (G.dimension + 1)).module
  apply InvariantGap.Construction.uniform_gap_of_discrete_invariant
    (E := Matrix (Fin G.dimension) (Fin G.dimension) (mixedSpace k))
    (F := Fin (G.dimension + 1) → mixedSpace k)
    (fun (g : Matrix.GeneralLinearGroup (Fin G.dimension) (mixedSpace k)) x => g.val * x * (g⁻¹).val)
    CharacteristicInvariant.Construction.characteristicInvariant CharacteristicInvariant.Construction.continuous_characteristicInvariant CharacteristicInvariant.Construction.characteristicInvariant_zero
    (D : Set (Fin (G.dimension + 1) → mixedSpace k))
    (isDiscrete_iff_discreteTopology.mpr
      (IntegralLattice.Construction.vectorLatticeImage_discrete _ (IntegralLattice.FullLattice.standard k (G.dimension + 1)).finite))
    D.zero_mem (integralLieMixedSet G)
    (characteristicInvariant_integralLie_values G haniso)
  exact fun g x _ => CharacteristicInvariant.Construction.characteristicInvariant_conjugate g x

theorem integral_matrix_mixedEmbedding_injective
    {k : Type} [Field k] [NumberField k] {n : ℕ} :
    Function.Injective (fun A : Matrix (Fin n) (Fin n) (𝓞 k) =>
      A.map ((mixedEmbedding k).comp (algebraMap (𝓞 k) k))) := by
  intro A B h
  ext i j : 1
  apply Subtype.ext
  apply mixedEmbedding_injective k
  exact congrFun (congrFun h i) j

theorem anisotropic_integral_lie_uniform_conjugation_gap
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ g : Matrix.GeneralLinearGroup (Fin G.dimension) (mixedSpace k),
      ∀ A : Matrix (Fin G.dimension) (Fin G.dimension) (𝓞 k),
        A.map (algebraMap (𝓞 k) k) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup → A ≠ 0 →
        ε ≤ ‖g.val * A.map ((mixedEmbedding k).comp (algebraMap (𝓞 k) k)) * (g⁻¹).val‖ := by
  obtain ⟨ε, hε, hgap⟩ := anisotropic_integralLie_uniform_gap G haniso
  refine ⟨ε, hε, fun g A hA hA0 => hgap g _ ⟨A, hA, rfl⟩ ?_⟩
  intro h
  apply hA0
  apply integral_matrix_mixedEmbedding_injective (k := k)
  exact h.trans (Matrix.map_zero _ (map_zero _)).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.CharacteristicGap.Construction

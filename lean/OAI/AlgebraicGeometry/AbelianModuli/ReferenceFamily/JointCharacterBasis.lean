import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointCharacterDecomposition
import Mathlib.LinearAlgebra.StdBasis

/-! # Joint Character Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointCharacterBasis

noncomputable section

/-! Finite character dimensions that exhaust the ambient dimension
give an actual basis, indexed by the bases of the joint eigenspaces. -/

open scoped BigOperators

variable {k V R I : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Fintype I] [DecidableEq I]
    (ρ : R → V →ₗ[k] V) (χ : I → R → k)

omit [FiniteDimensional k V] in
theorem jointCharacterSumLinear_single (i : I) (v : JointCharacterDecomposition.jointCharacterSpace ρ (χ i)) :
    JointCharacterDecomposition.jointCharacterSumLinear ρ χ (Pi.single i v) = v.val := by
  change (∑ j, ((Pi.single i v : ∀ j, JointCharacterDecomposition.jointCharacterSpace ρ (χ j)) j).val) = v.val
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

def jointCharacterBasis (hχ : Function.Injective χ)
    (hdim : (∑ i, Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i))) = Module.finrank k V) :
    Module.Basis (Σ i, Fin (Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i)))) k V :=
  (Pi.basis (fun i => Module.finBasis k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i)))).map
    (JointCharacterDecomposition.jointCharacterDecomposition ρ χ hχ hdim)

theorem jointCharacterBasis_apply (hχ : Function.Injective χ)
    (hdim : (∑ i, Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i))) = Module.finrank k V)
    (j : Σ i, Fin (Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i)))) :
    jointCharacterBasis ρ χ hχ hdim j =
      (Module.finBasis k (JointCharacterDecomposition.jointCharacterSpace ρ (χ j.1)) j.2).val := by
  rw [jointCharacterBasis, Module.Basis.map_apply, Pi.basis_apply]
  exact jointCharacterSumLinear_single ρ χ j.1 _

theorem jointCharacterBasis_eigen (hχ : Function.Injective χ)
    (hdim : (∑ i, Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i))) = Module.finrank k V)
    (j : Σ i, Fin (Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i)))) (a : R) :
    ρ a (jointCharacterBasis ρ χ hχ hdim j) =
      χ j.1 a • jointCharacterBasis ρ χ hχ hdim j := by
  rw [jointCharacterBasis_apply]
  exact (Module.finBasis k (JointCharacterDecomposition.jointCharacterSpace ρ (χ j.1)) j.2).property a

def jointCharacterBasisOfRanks (hχ : Function.Injective χ) (r : I → ℕ)
    (hr : ∀ i, Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i)) = r i)
    (hdim : (∑ i, r i) = Module.finrank k V) : Module.Basis (Σ i, Fin (r i)) k V :=
  (Pi.basis (fun i => (Module.finBasis k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i))).reindex
    (finCongr (hr i)))).map
      (JointCharacterDecomposition.jointCharacterDecomposition ρ χ hχ
        ((Finset.sum_congr rfl (fun i _ => hr i)).trans hdim))

theorem jointCharacterBasisOfRanks_apply (hχ : Function.Injective χ) (r : I → ℕ)
    (hr : ∀ i, Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i)) = r i)
    (hdim : (∑ i, r i) = Module.finrank k V) (j : Σ i, Fin (r i)) :
    jointCharacterBasisOfRanks ρ χ hχ r hr hdim j =
      ((Module.finBasis k (JointCharacterDecomposition.jointCharacterSpace ρ (χ j.1))).reindex
        (finCongr (hr j.1)) j.2).val := by
  rw [jointCharacterBasisOfRanks, Module.Basis.map_apply, Pi.basis_apply]
  exact jointCharacterSumLinear_single ρ χ j.1 _

theorem jointCharacterBasisOfRanks_eigen (hχ : Function.Injective χ) (r : I → ℕ)
    (hr : ∀ i, Module.finrank k (JointCharacterDecomposition.jointCharacterSpace ρ (χ i)) = r i)
    (hdim : (∑ i, r i) = Module.finrank k V) (j : Σ i, Fin (r i)) (a : R) :
    ρ a (jointCharacterBasisOfRanks ρ χ hχ r hr hdim j) =
      χ j.1 a • jointCharacterBasisOfRanks ρ χ hχ r hr hdim j := by
  rw [jointCharacterBasisOfRanks_apply]
  exact ((Module.finBasis k (JointCharacterDecomposition.jointCharacterSpace ρ (χ j.1))).reindex
    (finCongr (hr j.1)) j.2).property a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointCharacterBasis

import OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicAdjointNilpotents
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Characteristic Invariant -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CharacteristicInvariant.Construction

noncomputable section

/-! The non-leading characteristic coefficients are continuous integral
polynomial invariants that detect nilpotence. -/

open scoped Classical
open _root_.Matrix _root_.Polynomial

def characteristicInvariant {R : Type} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : Fin (n + 1) → R :=
  fun i => (A.charpoly - Polynomial.X ^ n).coeff i.val

theorem characteristicInvariant_map
    {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (ι : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) :
    characteristicInvariant (A.map ι) = fun i => ι (characteristicInvariant A i) := by
  funext i
  simp only [characteristicInvariant, Matrix.charpoly_map, Polynomial.coeff_sub,
    Polynomial.coeff_map, map_sub, Polynomial.coeff_X_pow, apply_ite ι, map_one, map_zero]

theorem characteristicInvariant_conjugate
    {R : Type} [CommRing R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) (A : Matrix (Fin n) (Fin n) R) :
    characteristicInvariant (g.val * A * (g⁻¹).val) = characteristicInvariant A := by
  unfold characteristicInvariant
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.charpoly_units_conj]

theorem characteristicInvariant_zero
    {R : Type} [CommRing R] {n : ℕ} :
    characteristicInvariant (0 : Matrix (Fin n) (Fin n) R) = 0 := by
  funext i
  change ((0 : Matrix (Fin n) (Fin n) R).charpoly - Polynomial.X ^ n).coeff i.val = 0
  rw [Matrix.charpoly_zero, Fintype.card_fin, sub_self, Polynomial.coeff_zero]

theorem nilpotent_of_characteristicInvariant_eq_zero
    {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (hA : characteristicInvariant A = 0) : IsNilpotent A := by
  have hp : A.charpoly = Polynomial.X ^ n := by
    apply Polynomial.ext
    intro i
    by_cases hi : i < n + 1
    · have h := congrFun hA ⟨i, hi⟩
      change (A.charpoly - Polynomial.X ^ n).coeff i = 0 at h
      rw [Polynomial.coeff_sub] at h
      exact sub_eq_zero.mp h
    · have hni : n < i := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hni : A.charpoly.natDegree < i)]
      symm
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hni)
  refine ⟨n, ?_⟩
  rw [← Polynomial.aeval_X_pow (R := k), ← hp]
  exact Matrix.aeval_self_charpoly A

theorem continuous_characteristicInvariant
    {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ} :
    Continuous (characteristicInvariant : Matrix (Fin n) (Fin n) R → Fin (n + 1) → R) := by
  apply continuous_pi
  intro i
  change Continuous (fun A : Matrix (Fin n) (Fin n) R =>
    (A.charpoly - Polynomial.X ^ n).coeff i.val)
  simp_rw [Polynomial.coeff_sub]
  apply Continuous.sub _ continuous_const
  have he (A : Matrix (Fin n) (Fin n) R) :
      MvPolynomial.eval (fun ij : Fin n × Fin n => A ij.1 ij.2)
        ((Matrix.charpoly.univ R (Fin n)).coeff i.val) = A.charpoly.coeff i.val :=
    Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id R) _ i.val
  simp_rw [← he]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro ij
  exact (continuous_apply ij.2).comp (continuous_apply ij.1)

theorem anisotropic_characteristicInvariant_ne_zero
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G)
    (A : Matrix (Fin G.dimension) (Fin G.dimension) k)
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) (hA0 : A ≠ 0) :
    characteristicInvariant A ≠ 0 := by
  intro h
  exact hA0 (AnisotropicAdjointNilpotents.Construction.anisotropic_infinitesimal_nilpotent_eq_zero G haniso A hA
    (nilpotent_of_characteristicInvariant_eq_zero A h))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CharacteristicInvariant.Construction

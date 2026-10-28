import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.MvPolynomial.Equiv
import Lean.Util.CollectAxioms

/-! # Countable Algebra -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CountableAlgebra

noncomputable section

/-!
The algebraic dimension step in descent from a countable parameter set.
Noether normalization and lying over show that a finite-type algebra over
an uncountable field with only countably many maximal ideals is finite
over that field.
-/

universe u

variable {R A : Type u} [CommRing R] [CommRing A]

def integralMaximalComap (f : R →+* A) (hf : f.IsIntegral) :
    MaximalSpectrum A → MaximalSpectrum R := fun p ↦
  ⟨p.asIdeal.comap f, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf p.asIdeal⟩

theorem integralMaximalComap_surjective (f : R →+* A) (hf : f.IsIntegral)
    (hinj : Function.Injective f) : Function.Surjective (integralMaximalComap f hf) := by
  let : Algebra R A := f.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hf⟩
  intro p
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) p.asIdeal (by
    change RingHom.ker f ≤ p.asIdeal
    rw [(RingHom.injective_iff_ker_eq_bot f).mp hinj]
    exact bot_le)
  exact ⟨⟨q, hq⟩, MaximalSpectrum.ext hqp⟩

variable (k : Type u) [Field k]

/-- Distinct scalars give distinct maximal ideals in any nontrivial
polynomial variable. -/
def diagonalMaximalIdeal (n : ℕ) (c : k) : MaximalSpectrum (MvPolynomial (Fin n) k) :=
  ⟨RingHom.ker (MvPolynomial.aeval (fun _ : Fin n ↦ c)).toRingHom,
    Ideal.comap_isMaximal_of_surjective _ (by
      intro a
      exact ⟨MvPolynomial.C a, by simp⟩)⟩

theorem diagonalMaximalIdeal_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (diagonalMaximalIdeal k n) := by
  intro c d h
  have heq := congrArg MaximalSpectrum.asIdeal h
  have hm : MvPolynomial.X (⟨0, hn⟩ : Fin n) - MvPolynomial.C c ∈
      (diagonalMaximalIdeal k n c).asIdeal := by
    change (MvPolynomial.aeval (fun _ : Fin n ↦ c)) _ = 0
    simp
  rw [heq] at hm
  change (MvPolynomial.aeval (fun _ : Fin n ↦ d)) _ = 0 at hm
  have hd : d - c = 0 := by simpa using hm
  exact (sub_eq_zero.mp hd).symm

/-- Countably many maximal ideals force dimension zero over an
uncountable field. Finiteness over the base is the actual conclusion. -/
theorem finite_of_countable_maximalSpectrum
    [Uncountable k] (A : Type u) [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A] [Countable (MaximalSpectrum A)] : Module.Finite k A := by
  obtain ⟨n, f, hinj, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  have hc : Countable (MaximalSpectrum (MvPolynomial (Fin n) k)) :=
    (integralMaximalComap_surjective f.toRingHom (RingHom.Finite.to_isIntegral hfinite) hinj).countable
  have hn : n = 0 := by
    by_contra h
    exact not_countable (α := k)
      (diagonalMaximalIdeal_injective k n (Nat.pos_of_ne_zero h)).countable
  subst n
  let : Algebra (MvPolynomial (Fin 0) k) A := f.toRingHom.toAlgebra
  let : IsScalarTower k (MvPolynomial (Fin 0) k) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  have : Module.Finite (MvPolynomial (Fin 0) k) A := hfinite
  have : Module.Finite k (MvPolynomial (Fin 0) k) :=
    Module.Finite.of_surjective (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.toLinearMap
      (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.surjective
  exact Module.Finite.trans (MvPolynomial (Fin 0) k) A

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CountableAlgebra

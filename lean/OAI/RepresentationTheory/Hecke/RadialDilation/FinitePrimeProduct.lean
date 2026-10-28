import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskCoordinates
import Mathlib.Data.Finset.NoncommProd

/-! # Finite Prime Product -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimeProduct.Realization

noncomputable section

/-! The part at a finite set of primes is a product of commuting one-prime matrices. -/

open scoped Classical _root_.Matrix
open _root_.Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finitePrimePart (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (v : HeightOneSpectrum ℤ) : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf :=
  FiniteConjugation.Realization.finitePrimeSymplecticInclusion v (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) g)

theorem finitePrimePart_eval (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (v w : HeightOneSpectrum ℤ) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval w) (finitePrimePart g v) =
      if w = v then Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval w) g else 1 := by
  by_cases hw : w = v
  · subst w
    rw [ite_eq_left rfl]
    exact FiniteConjugation.Realization.finitePrimeSymplecticInclusion_projection v _
  · rw [ite_eq_right hw]
    exact FiniteMaskCoordinates.Realization.finitePrimeSymplecticInclusion_other v w hw _

theorem finitePrimePart_commute (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (v w : HeightOneSpectrum ℤ) (hvw : v ≠ w) :
    Commute (finitePrimePart g v) (finitePrimePart g w) := by
  apply FiniteMaskCoordinates.Realization.finiteSymplectic_ext
  intro u
  rw [map_mul, map_mul, finitePrimePart_eval, finitePrimePart_eval]
  by_cases huv : u = v
  · subst u
    simp [hvw]
  · simp [huv]

theorem finiteMaskSymplectic_empty (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) : FiniteMaskedGenerators.Realization.finiteMaskSymplectic ∅ g = 1 := by
  apply FiniteMaskCoordinates.Realization.finiteSymplectic_ext
  intro v
  rw [FiniteMaskedGenerators.Realization.finiteMaskSymplectic_projection, map_one]
  simp

theorem finiteMaskSymplectic_insert (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (S : Finset (HeightOneSpectrum ℤ))
    (v : HeightOneSpectrum ℤ) (hv : v ∉ S) :
    FiniteMaskedGenerators.Realization.finiteMaskSymplectic (insert v S : Set (HeightOneSpectrum ℤ)) g =
      finitePrimePart g v * FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ)) g := by
  apply FiniteMaskCoordinates.Realization.finiteSymplectic_ext
  intro w
  rw [map_mul, FiniteMaskedGenerators.Realization.finiteMaskSymplectic_projection, finitePrimePart_eval, FiniteMaskedGenerators.Realization.finiteMaskSymplectic_projection]
  by_cases hw : w = v
  · subst w
    simp [hv]
  · by_cases hs : w ∈ S <;> simp [hw, hs]

theorem finitePrimePart_pairwise (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (S : Finset (HeightOneSpectrum ℤ)) :
    (S : Set (HeightOneSpectrum ℤ)).Pairwise (Function.onFun Commute (finitePrimePart g)) := by
  intro v _ w _ hvw
  exact finitePrimePart_commute g v w hvw

theorem finiteMaskSymplectic_finite_product (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (S : Finset (HeightOneSpectrum ℤ)) :
    FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ)) g =
      S.noncommProd (finitePrimePart g) (finitePrimePart_pairwise g S) := by
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.noncommProd_empty]
      simpa only [Finset.coe_empty] using finiteMaskSymplectic_empty g
  | @insert v S hv ih =>
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hv, ← ih]
      simpa only [Finset.coe_insert] using finiteMaskSymplectic_insert g S v hv

theorem finiteMaskSymplectic_mem_of_prime_parts (H : Subgroup (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf))
    (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ v ∈ S, finitePrimePart g v ∈ H) :
    FiniteMaskedGenerators.Realization.finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ)) g ∈ H := by
  rw [finiteMaskSymplectic_finite_product]
  exact Finset.noncommProd_induction S (finitePrimePart g) _ (fun h => h ∈ H)
    (fun _ _ => H.mul_mem) H.one_mem hS

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimeProduct.Realization

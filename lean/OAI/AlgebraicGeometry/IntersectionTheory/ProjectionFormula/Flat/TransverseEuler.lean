import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OneSidedTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Transverse Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.TransverseEuler

noncomputable section

/-! The local transverse intersection calculation: a quotient pulled
back through a flat algebra has no higher Tor against another algebra
flat over the same base. An unramified local closed fiber has length one. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Module.Flat R S] [Module.Flat R T]

def quotientEquiv (I : Ideal R) :
    (S ⧸ I.map (algebraMap R S)) ≃ₗ[S] S ⊗[R] (R ⧸ I) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toLinearEquiv

theorem higher_length (I : Ideal R) (n : ℕ) :
    Module.length S (((Tor (ModuleCat S) (n + 1)).obj
      (.of S (S ⧸ I.map (algebraMap R S)))).obj (.of S T)) = 0 := by
  rw [Open.SupportTor.length_iso S (quotientEquiv R S I).toModuleIso
    (Iso.refl (.of S T))]
  exact OneSidedTor.higher_length R S (.of R (R ⧸ I)) (.of S T) n

theorem euler_length (I : Ideal R) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length S (((Tor (ModuleCat S) i).obj
        (.of S (S ⧸ I.map (algebraMap R S)))).obj (.of S T))).toNat) =
      (Module.length S (T ⧸ I.map (algebraMap R T))).toNat := by
  have he (i : ℕ) := Open.SupportTor.length_iso S (quotientEquiv R S I).toModuleIso
    (Iso.refl (.of S T)) i
  simp_rw [he]
  trans ((Module.length S (T ⊗[R] (R ⧸ I))).toNat : ℚ)
  · exact OneSidedTor.euler_length R S (.of R (R ⧸ I)) (.of S T) d
  exact congrArg (fun l : ℕ∞ => (l.toNat : ℚ))
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toLinearEquiv.restrictScalars S).length_eq

theorem euler_one [IsLocalRing R] [IsLocalRing T]
    (hST : Function.Surjective (algebraMap S T))
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R T) = IsLocalRing.maximalIdeal T)
    (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length S (((Tor (ModuleCat S) i).obj
        (.of S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)))).obj (.of S T))).toNat) = 1 := by
  rw [euler_length, hmax, Module.length_eq_of_surjective hST]
  have hl : Module.length T (T ⧸ IsLocalRing.maximalIdeal T) = 1 := by
    rw [Module.length_eq_of_surjective (M := T ⧸ IsLocalRing.maximalIdeal T)
      (show Function.Surjective (algebraMap T (T ⧸ IsLocalRing.maximalIdeal T)) from
        Ideal.Quotient.mk_surjective)]
    exact Module.length_eq_one (IsLocalRing.ResidueField T) (IsLocalRing.ResidueField T)
  rw [hl]
  norm_num

theorem euler_one_of_unramified [IsLocalRing R] [IsLocalRing T]
    [IsLocalHom (algebraMap R T)] [Algebra.EssFiniteType R T]
    [Algebra.FormallyUnramified R T] (hST : Function.Surjective (algebraMap S T)) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length S (((Tor (ModuleCat S) i).obj
        (.of S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)))).obj (.of S T))).toNat) = 1 :=
  euler_one R S T hST Algebra.FormallyUnramified.map_maximalIdeal d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.TransverseEuler

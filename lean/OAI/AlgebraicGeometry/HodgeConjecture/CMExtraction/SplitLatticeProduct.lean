import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TensorEvaluation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi

/-! # Split Lattice Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeProduct.TestTransport

noncomputable section

/-! Integral splitting separates the local components of a stable
lattice. The product equality is proved using the actual integral
idempotents supplied by the surjective tensor completion map. -/

open scoped Classical TensorProduct

variable {A E R K S I : Type*} [CommRing A] [CommRing E] [CommRing R] [CommRing K]
  [Algebra R K] [Fintype S] [DecidableEq S]
  (ι : A →+* E) (σ : S → E →+* K) (χ : S → A →+* R)
  (hχ : ∀ v a, algebraMap R K (χ v a) = σ v (ι a))

def splitIntegralTensorMap : R ⊗[ℤ] A →ₐ[ℤ] (S → R) :=
  TensorEvaluation.TestTransport.tensorEvaluation (algebraMap R (S → R)).toIntAlgHom (RingHom.pi χ).toIntAlgHom

def splitLatticeImage (L : Submodule ℤ (I → E)) : Submodule R (S → I → K) :=
  Submodule.span R ((fun x : I → E => fun v i => σ v (x i)) '' (L : Set (I → E)))

def splitLatticeLocal (L : Submodule ℤ (I → E)) (v : S) : Submodule R (I → K) :=
  Submodule.span R ((fun x : I → E => fun i => σ v (x i)) '' (L : Set (I → E)))

variable (L : Submodule ℤ (I → E))
  (hL : ∀ a : A, ∀ x ∈ L, ι a • x ∈ L)

include hχ hL in
omit [Fintype S] [DecidableEq S] in
theorem splitLatticeImage_action (a : A) (x : S → I → K) (hx : x ∈ splitLatticeImage (R := R) σ L) :
    (fun v i => algebraMap R K (χ v a) * x v i) ∈ splitLatticeImage (R := R) σ L := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨ι a • y, hL a y hy, ?_⟩
      funext v i
      change σ v (ι a * y i) = algebraMap R K (χ v a) * σ v (y i)
      rw [map_mul, hχ]
  | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact (splitLatticeImage (R := R) σ L).zero_mem
  | add x y _ _ hx hy =>
      have h := (splitLatticeImage (R := R) σ L).add_mem hx hy
      change (fun v i => algebraMap R K (χ v a) * x v i +
        algebraMap R K (χ v a) * y v i) ∈ splitLatticeImage (R := R) σ L at h
      simpa only [Pi.add_apply, mul_add] using h
  | smul r x _ hx =>
      have h := (splitLatticeImage (R := R) σ L).smul_mem r hx
      change (fun v i => r • (algebraMap R K (χ v a) * x v i)) ∈
        splitLatticeImage (R := R) σ L at h
      simpa only [Pi.smul_apply, Algebra.smul_def, mul_left_comm] using h

include hχ hL in
omit [Fintype S] [DecidableEq S] in
theorem splitLatticeImage_tensor_action (t : R ⊗[ℤ] A)
    (x : S → I → K) (hx : x ∈ splitLatticeImage (R := R) σ L) :
    (fun v i => algebraMap R K (splitIntegralTensorMap χ t v) * x v i) ∈ splitLatticeImage (R := R) σ L := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
      have h := (splitLatticeImage (R := R) σ L).add_mem ht hu
      change (fun v i => algebraMap R K (splitIntegralTensorMap χ t v) * x v i +
        algebraMap R K (splitIntegralTensorMap χ u v) * x v i) ∈ splitLatticeImage (R := R) σ L at h
      simpa only [map_add, Pi.add_apply, add_mul] using h
  | tmul r a =>
      have h := (splitLatticeImage (R := R) σ L).smul_mem r (splitLatticeImage_action ι σ χ hχ L hL a x hx)
      change (fun v i => r • (algebraMap R K (χ v a) * x v i)) ∈
        splitLatticeImage (R := R) σ L at h
      change (fun v i => algebraMap R K (r * χ v a) * x v i) ∈ splitLatticeImage (R := R) σ L
      simpa only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc] using h

include hχ hL in
omit [Fintype S] in
theorem splitLatticeImage_mask (hs : Function.Surjective (splitIntegralTensorMap χ))
    (v : S) (x : S → I → K) (hx : x ∈ splitLatticeImage (R := R) σ L) :
    Pi.single v (x v) ∈ splitLatticeImage (R := R) σ L := by
  obtain ⟨t, ht⟩ := hs (Pi.single v 1)
  have h := splitLatticeImage_tensor_action ι σ χ hχ L hL t x hx
  rw [ht] at h
  have he : (fun w i => algebraMap R K ((Pi.single v (1 : R) : S → R) w) * x w i) = Pi.single v (x v) := by
    funext w i
    by_cases hw : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne hw]
  exact he ▸ h

omit [Fintype S] [DecidableEq S] in
theorem splitLatticeImage_projection (v : S) :
    (splitLatticeImage (R := R) σ L).map (LinearMap.proj v) = splitLatticeLocal (R := R) σ L v := by
  rw [splitLatticeImage, Submodule.map_span]
  congr 1
  rw [Set.image_image]
  rfl

include hχ hL in
theorem splitLatticeImage_eq_product (hs : Function.Surjective (splitIntegralTensorMap χ)) :
    splitLatticeImage (R := R) σ L = Submodule.pi Set.univ (splitLatticeLocal (R := R) σ L) := by
  ext x
  constructor
  · intro hx v _
    change x v ∈ splitLatticeLocal (R := R) σ L v
    rw [← splitLatticeImage_projection σ L v]
    exact ⟨x, hx, rfl⟩
  · intro hx
    have hm (v : S) : Pi.single v (x v) ∈ splitLatticeImage (R := R) σ L := by
      have hv := hx v (Set.mem_univ v)
      change x v ∈ splitLatticeLocal (R := R) σ L v at hv
      rw [← splitLatticeImage_projection σ L v] at hv
      obtain ⟨y, hy, he⟩ := hv
      have h := splitLatticeImage_mask ι σ χ hχ L hL hs v y hy
      change y v = x v at he
      rwa [he] at h
    have hsum := (splitLatticeImage (R := R) σ L).sum_mem (t := Finset.univ) (fun v _ => hm v)
    simpa only [Finset.univ_sum_single] using hsum

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeProduct.TestTransport

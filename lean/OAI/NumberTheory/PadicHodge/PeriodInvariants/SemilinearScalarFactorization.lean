import Mathlib.LinearAlgebra.Pi

/-! # Semilinear Scalar Factorization -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearScalarFactorization

noncomputable section

/-! # Scalar finite-free splittings transport across compatible changes of residue rings -/

variable {R S M N ι : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] (e : R ≃+* S)

local instance forwardPair : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e

local instance backwardPair : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.symm e.toRingHom e.symm.toRingHom

variable (E : M ≃ₛₗ[e.toRingHom] N)

def forward (f : N →ₗ[S] (ι → S)) : M →ₗ[R] (ι → R) where
  toFun x i := e.symm (f (E x) i)
  map_add' x y := by
    ext i
    simp only [map_add, Pi.add_apply]
  map_smul' a x := by
    ext i
    simp only [RingHom.id_apply, LinearEquiv.map_smulₛₗ, map_smul, Pi.smul_apply, smul_eq_mul,
      map_mul]
    change e.symm (e a) * e.symm (f (E x) i) = _
    rw [e.symm_apply_apply]

def backward (g : (ι → S) →ₗ[S] N) : (ι → R) →ₗ[R] M where
  toFun c := E.symm (g (fun i => e (c i)))
  map_add' x y := by
    change E.symm (g (fun i => e (x i + y i))) = _
    simp only [map_add]
    change E.symm (g ((fun i => e (x i)) + (fun i => e (y i)))) = _
    rw [map_add, map_add]
  map_smul' a c := by
    change E.symm (g (fun i => e (a * c i))) = a • E.symm (g (fun i => e (c i)))
    simp only [map_mul]
    change E.symm (g (e a • (fun i => e (c i)))) = _
    rw [map_smul, LinearEquiv.map_smulₛₗ]
    change e.symm (e a) • E.symm (g (fun i => e (c i))) = _
    rw [e.symm_apply_apply]

theorem factorization (f : N →ₗ[S] (ι → S)) (g : (ι → S) →ₗ[S] N)
    (a : S) (h : g.comp f = a • LinearMap.id) :
    (backward e E g).comp (forward e E f) = e.symm a • LinearMap.id := by
  apply LinearMap.ext
  intro x
  change E.symm (g (fun i => e (e.symm (f (E x) i)))) = e.symm a • x
  simp only [e.apply_symm_apply]
  have hx := LinearMap.congr_fun h (E x)
  change g (f (E x)) = a • E x at hx
  rw [hx, LinearEquiv.map_smulₛₗ, E.symm_apply_apply]
  rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearScalarFactorization

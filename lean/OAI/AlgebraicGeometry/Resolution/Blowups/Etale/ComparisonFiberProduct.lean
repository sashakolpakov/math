import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Comparison Fiber Product -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ComparisonFiberProduct.Construction

noncomputable section

/-! The actual affine fiber product used to compare two étale coordinate charts. -/

open scoped TensorProduct

universe u

variable {k P R S : Type u} [CommRing k] [CommRing P] [CommRing R] [CommRing S]
  [Algebra k P] [Algebra k R] [Algebra k S] [Algebra P R] [Algebra P S]
  [IsScalarTower k P R] [IsScalarTower k P S]

def etaleComparisonLeft : R →ₐ[k] R ⊗[P] S := Algebra.TensorProduct.includeLeft

def etaleComparisonRight : S →ₐ[k] R ⊗[P] S :=
  (Algebra.TensorProduct.includeRight : S →ₐ[P] R ⊗[P] S).restrictScalars k

theorem etaleComparison_coordinate_relation (p : P) :
    etaleComparisonLeft (k := k) (P := P) (S := S) (algebraMap P R p) =
      etaleComparisonRight (k := k) (P := P) (R := R) (algebraMap P S p) := by
  exact ((Algebra.TensorProduct.includeLeft : R →ₐ[P] R ⊗[P] S).commutes p).trans
    ((Algebra.TensorProduct.includeRight : S →ₐ[P] R ⊗[P] S).commutes p).symm

omit [Algebra k S] [IsScalarTower k P S] in
theorem etaleComparisonLeft_etale [Algebra.Etale P S] :
    (etaleComparisonLeft (k := k) (P := P) (R := R) (S := S)).toRingHom.Etale := by
  change (algebraMap R (R ⊗[P] S)).Etale
  exact RingHom.etale_algebraMap.mpr inferInstance

theorem etaleComparisonRight_etale [Algebra.Etale P R] :
    (etaleComparisonRight (k := k) (P := P) (R := R) (S := S)).toRingHom.Etale := by
  have he : (etaleComparisonRight (k := k) (P := P) (R := R) (S := S)).toRingHom =
      (Algebra.TensorProduct.comm P S R).toRingHom.comp (algebraMap S (S ⊗[P] R)) := by
    ext s
    simp [etaleComparisonRight, Algebra.TensorProduct.algebraMap_apply]
  rw [he]
  exact RingHom.Etale.stableUnderComposition
    (algebraMap S (S ⊗[P] R)) (Algebra.TensorProduct.comm P S R).toRingHom
    ((RingHom.etale_algebraMap (R := S) (S := S ⊗[P] R)).mpr inferInstance)
    (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm P S R).bijective)

variable {C : Type u} [CommRing C] [Algebra k C]

/-- Compatible points of the two coordinate charts give a point on their actual
fiber product, retaining the original coefficient algebra. -/
def etaleComparisonPoint (r : R →ₐ[k] C) (s : S →ₐ[k] C)
    (h : ∀ p : P, r (algebraMap P R p) = s (algebraMap P S p)) :
    R ⊗[P] S →ₐ[k] C := by
  let : Algebra P C := (r.toRingHom.comp (algebraMap P R)).toAlgebra
  let : IsScalarTower k P C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap k C a = r (algebraMap P R (algebraMap k P a))
    rw [← IsScalarTower.algebraMap_apply k P R, r.commutes])
  let rP : R →ₐ[P] C := { r.toRingHom with commutes' := fun _ => rfl }
  let sP : S →ₐ[P] C := { s.toRingHom with commutes' := fun p => (h p).symm }
  exact (Algebra.TensorProduct.lift rP sP (fun _ _ => Commute.all _ _)).restrictScalars k

omit [IsScalarTower k P S] in
theorem etaleComparisonPoint_left (r : R →ₐ[k] C) (s : S →ₐ[k] C)
    (h : ∀ p : P, r (algebraMap P R p) = s (algebraMap P S p)) (x : R) :
    etaleComparisonPoint r s h (etaleComparisonLeft (k := k) (P := P) (S := S) x) = r x := by
  change r x * s 1 = r x
  rw [map_one, mul_one]

theorem etaleComparisonPoint_right (r : R →ₐ[k] C) (s : S →ₐ[k] C)
    (h : ∀ p : P, r (algebraMap P R p) = s (algebraMap P S p)) (x : S) :
    etaleComparisonPoint r s h (etaleComparisonRight (k := k) (P := P) (R := R) x) = s x := by
  change r 1 * s x = s x
  rw [map_one, one_mul]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ComparisonFiberProduct.Construction

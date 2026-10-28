import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Determinant Basis Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantBasisNeighborhood

noncomputable section

/-! Prescribed vectors become the literal basis on the principal determinant open.
If they form a basis after a coefficient quotient, that open contains the whole quotient. -/

open _root_.Module
open scoped TensorProduct

universe u v w t
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {ι : Type w} [Fintype ι] [DecidableEq ι]
  (b : Basis ι R M) (x : ι → M)
  (S : Type t) [CommRing S] [Algebra R S]

theorem det_baseChange :
    (b.baseChange S).det (fun i => (1 : S) ⊗ₜ[R] x i) =
      algebraMap R S (b.det x) := by
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, Basis.baseChange_repr_tmul, Algebra.smul_def]

include b in
theorem image_isUnit (c : Basis ι S (S ⊗[R] M))
    (hc : ∀ i, c i = (1 : S) ⊗ₜ[R] x i) :
    IsUnit (algebraMap R S (b.det x)) := by
  rw [← det_baseChange b x S]
  have h : (fun i => (1 : S) ⊗ₜ[R] x i) = c := funext (fun i => (hc i).symm)
  rw [h]
  exact (b.baseChange S).isUnit_det c

def basisOfIsUnitImage (h : IsUnit (algebraMap R S (b.det x))) :
    Basis ι S (S ⊗[R] M) :=
  Basis.mk
    (((b.baseChange S).is_basis_iff_det.mpr (by rw [det_baseChange]; exact h)).1)
    (((b.baseChange S).is_basis_iff_det.mpr (by rw [det_baseChange]; exact h)).2.ge)

theorem basisOfIsUnitImage_apply (h : IsUnit (algebraMap R S (b.det x))) (i : ι) :
    basisOfIsUnitImage b x S h i = (1 : S) ⊗ₜ[R] x i :=
  Basis.mk_apply _ _ _

def localizedBasis :
    Basis ι (Localization.Away (b.det x)) (Localization.Away (b.det x) ⊗[R] M) :=
  basisOfIsUnitImage b x _ (IsLocalization.Away.algebraMap_isUnit (b.det x))

theorem localizedBasis_apply (i : ι) :
    localizedBasis b x i = (1 : Localization.Away (b.det x)) ⊗ₜ[R] x i :=
  basisOfIsUnitImage_apply b x _ _ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantBasisNeighborhood

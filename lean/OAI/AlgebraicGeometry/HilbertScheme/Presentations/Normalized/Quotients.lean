import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Matrices
import Mathlib.RingTheory.Grassmannian

/-! # Quotients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients.Grassmannian

noncomputable section

/-!
Normalized matrices classify genuine quotient submodules. Their quotient is
finite free, and fixed selected columns determine the matrix from its kernel.
-/

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

def selectedBasisMap (a : ι → ν) : (ι → R) →ₗ[R] (ν → R) :=
  Matrix.toLin' ((1 : Matrix ν ν R).submatrix id a)

theorem matrix_comp_selectedBasisMap (a : ι → ν) (Q : Matrix ι ν R) :
    (Matrix.toLin' Q).comp (selectedBasisMap a) = Matrix.toLin' (Matrices.Grassmannian.selectedColumns a Q) := by
  change (Matrix.toLin' Q).comp (Matrix.toLin' ((1 : Matrix ν ν R).submatrix id a)) = _
  rw [← Matrix.toLin'_mul]
  exact congrArg Matrix.toLin' (Matrix.mul_submatrix_one (Equiv.refl ν) a Q)

theorem normalizedMatrix_comp_selectedBasisMap (a : ι → ν) (Q : Matrix ι ν R)
    (h : Matrices.Grassmannian.IsNormalized a Q) : (Matrix.toLin' Q).comp (selectedBasisMap a) = LinearMap.id := by
  rw [matrix_comp_selectedBasisMap, h, Matrix.toLin'_one]

theorem normalizedMatrix_section (a : ι → ν) (Q : Matrix ι ν R)
    (h : Matrices.Grassmannian.IsNormalized a Q) (x : ι → R) :
    Matrix.toLin' Q (selectedBasisMap a x) = x :=
  LinearMap.congr_fun (normalizedMatrix_comp_selectedBasisMap a Q h) x

theorem normalizedMatrix_surjective (a : ι → ν) (Q : Matrix ι ν R)
    (h : Matrices.Grassmannian.IsNormalized a Q) : Function.Surjective (Matrix.toLin' Q) :=
  fun x => ⟨selectedBasisMap a x, normalizedMatrix_section a Q h x⟩

def normalizedQuotientEquiv (a : ι → ν) (Q : Matrix ι ν R) (h : Matrices.Grassmannian.IsNormalized a Q) :
    ((ν → R) ⧸ (Matrix.toLin' Q).ker) ≃ₗ[R] (ι → R) :=
  (Matrix.toLin' Q).quotKerEquivOfSurjective (normalizedMatrix_surjective a Q h)

theorem normalizedMatrix_eq_of_kernel_eq (a : ι → ν) (Q K : Matrix ι ν R)
    (hQ : Matrices.Grassmannian.IsNormalized a Q) (hK : Matrices.Grassmannian.IsNormalized a K)
    (hker : (Matrix.toLin' Q).ker = (Matrix.toLin' K).ker) : Q = K := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have hx : x - selectedBasisMap a (Matrix.toLin' Q x) ∈ (Matrix.toLin' Q).ker := by
    change Matrix.toLin' Q (x - selectedBasisMap a (Matrix.toLin' Q x)) = 0
    rw [map_sub, normalizedMatrix_section a Q hQ, sub_self]
  rw [hker] at hx
  change Matrix.toLin' K (x - selectedBasisMap a (Matrix.toLin' Q x)) = 0 at hx
  rw [map_sub, normalizedMatrix_section a K hK, sub_eq_zero] at hx
  exact hx.symm

def normalizedGrassmannian (a : ι → ν) (Q : Matrix ι ν R) (h : Matrices.Grassmannian.IsNormalized a Q) :
    Module.Grassmannian R (ν → R) (Fintype.card ι) where
  toSubmodule := (Matrix.toLin' Q).ker
  finite_quotient := Module.Finite.equiv (normalizedQuotientEquiv a Q h).symm
  projective_quotient := Module.Projective.of_equiv (normalizedQuotientEquiv a Q h).symm
  rankAtStalk_eq p := by
    have : Nontrivial R := Function.Surjective.nontrivial
      (f := Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
    rw [congrFun (Module.rankAtStalk_eq_of_equiv (normalizedQuotientEquiv a Q h)) p,
      Module.rankAtStalk_eq_finrank_of_free]
    simp

theorem normalizedGrassmannian_injective (a : ι → ν) :
    Function.Injective (fun Q : {Q : Matrix ι ν R // Matrices.Grassmannian.IsNormalized a Q} =>
      normalizedGrassmannian a Q.val Q.property) := by
  intro Q K h
  apply Subtype.ext
  exact normalizedMatrix_eq_of_kernel_eq a Q.val K.val Q.property K.property
    (congrArg Module.Grassmannian.toSubmodule h)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients.Grassmannian

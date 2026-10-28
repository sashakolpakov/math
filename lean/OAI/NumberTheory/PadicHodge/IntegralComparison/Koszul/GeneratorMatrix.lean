import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualCoordinateConormalBasis

/-! # Generator Matrix -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix

noncomputable section

/-! The determinant orientation for a change of actual Koszul equations.
For `s = A t`, the resolution map goes from `s` to `t`; its dual top map
is multiplication by `det A`. This is exactly the determinant of the
corresponding conormal basis change, reduced modulo the original ideal. -/

open _root_.CategoryTheory

universe u
variable (R : Type u) [CommRing R] {n : ℕ}

def equation (s : Fin n → R) : Module.Dual R (Fin n → R) :=
  ∑ i, s i • LinearMap.proj i

theorem equation_apply (s : Fin n → R) (v : Fin n → R) :
    equation R s v = ∑ i, s i * v i := by
  simp [equation]

theorem equation_matrix (s t : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i, s i = ∑ j, A i j * t j) :
    (equation R t).comp (Matrix.toLin' A.transpose) = equation R s := by
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  simpa [LinearMap.comp_apply, Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.mulVec, dotProduct, equation_apply, Matrix.transpose_apply, mul_comm, Pi.single_apply]
    using (h i).symm

def change (s t : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i, s i = ∑ j, A i j * t j) :
    Exterior.KoszulComplex.complex R (Fin n → R) (equation R s) ⟶
      Exterior.KoszulComplex.complex R (Fin n → R) (equation R t) :=
  Exterior.KoszulComplex.map R _ _ _ _ (Matrix.toLin' A.transpose)
    (equation_matrix R s t A h)

theorem dual_top (s t : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i, s i = ∑ j, A i j * t j)
    (a : Module.Dual R (⋀[R]^n (Fin n → R))) :
    a.comp ((change R s t A h).f n).hom = A.det • a := by
  have ht := Exterior.KoszulComplex.dual_top R _ (Pi.basisFun R (Fin n))
    (equation R s) (equation R t) (Matrix.toLin' A.transpose)
    (equation_matrix R s t A h) a
  simpa only [change, LinearMap.det_toLin', Matrix.det_transpose] using ht

variable {R} (I : Ideal R) (s t : Fin n → I)
  (b : Module.Basis (Fin n) (R ⧸ I) I.Cotangent)
  (hb : ∀ i, b i = I.toCotangent (t i))
  (A : Matrix (Fin n) (Fin n) R)
  (h : ∀ i, (s i).val = ∑ j, A i j * (t j).val)

include h in
theorem conormal_equation (i : Fin n) :
    I.toCotangent (s i) = ∑ j, (Ideal.Quotient.mk I (A i j)) • I.toCotangent (t j) := by
  have he : s i = ∑ j, A i j • t j := by
    apply Subtype.ext
    simpa using h i
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  exact (algebraMap_smul (R ⧸ I) (A i j) (I.toCotangent (t j))).symm

include hb h in
theorem conormal_matrix :
    b.toMatrix (fun i => I.toCotangent (s i)) =
      ((Ideal.Quotient.mk I).mapMatrix A).transpose := by
  ext i j
  rw [Module.Basis.toMatrix_apply, conormal_equation I s t A h j]
  simp only [← hb, map_sum, map_smul, Module.Basis.repr_self]
  simp [Matrix.transpose_apply, RingHom.mapMatrix_apply, Finsupp.single_apply]

include hb h in
theorem conormal_determinant :
    b.det (fun i => I.toCotangent (s i)) = Ideal.Quotient.mk I A.det := by
  rw [Module.Basis.det_apply, conormal_matrix I s t b hb A h,
    Matrix.det_transpose, ← RingHom.map_det]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix

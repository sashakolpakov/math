import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Type Eleven Bilinear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TypeElevenBilinear

noncomputable section

section

/-! Real bilinear forms attached to the actual type-(1,1) covectors. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def covectorBilinear (a : V [⋀^Fin 2]→L[ℝ] ℂ) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
  (MultilinearMap.ofSubsingletonₗ ℝ ℝ V ℂ (0 : Fin 1)).symm.toLinearMap.comp
    a.toContinuousMultilinearMap.toMultilinearMap.curryLeft

theorem covectorBilinear_apply (a : V [⋀^Fin 2]→L[ℝ] ℂ) (u v : V) :
    covectorBilinear a u v = a ![u, v] := by
  change a (Fin.cons u (fun _ : Fin 1 => v)) = a ![u, v]
  congr 1
  funext i
  fin_cases i <;> rfl

def realCovectorBilinear (a : V [⋀^Fin 2]→L[ℝ] ℂ) : LinearMap.BilinForm ℝ V :=
  (covectorBilinear a).compr₂ Complex.reLm

theorem realCovectorBilinear_apply (a : V [⋀^Fin 2]→L[ℝ] ℂ) (u v : V) :
    realCovectorBilinear a u v = (a ![u, v]).re :=
  congrArg Complex.re (covectorBilinear_apply a u v)

theorem realCovectorBilinear_self (a : V [⋀^Fin 2]→L[ℝ] ℂ) (u : V) :
    realCovectorBilinear a u u = 0 := by
  rw [realCovectorBilinear_apply]
  have hz : a ![u, u] = 0 := a.map_eq_zero_of_eq _ (by rfl : (![u, u] : Fin 2 → V) 0 = ![u, u] 1) (by decide)
  rw [hz, Complex.zero_re]

theorem realCovectorBilinear_skew (a : V [⋀^Fin 2]→L[ℝ] ℂ) (u v : V) :
    realCovectorBilinear a v u = - realCovectorBilinear a u v := by
  have h := realCovectorBilinear_self a (u + v)
  simp only [map_add, LinearMap.add_apply, realCovectorBilinear_self, zero_add, add_zero] at h
  linarith

variable [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

omit [IsScalarTower ℝ ℂ V] in
theorem typeElevenBilinear_I_I (a : V [⋀^Fin 2]→L[ℝ] ℂ)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 1 1 a) (u v : V) :
    realCovectorBilinear a (Complex.I • u) (Complex.I • v) = realCovectorBilinear a u v := by
  let z : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have h := ha z ![u, v]
  have he : (fun i : Fin 2 => (z : ℂ) • ![u, v] i) = ![Complex.I • u, Complex.I • v] := by
    funext i; fin_cases i <;> rfl
  rw [he] at h
  have hz : Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 z = 1 := by simp [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, z]
  rw [hz, one_mul] at h
  exact (realCovectorBilinear_apply a _ _).trans ((congrArg Complex.re h).trans (realCovectorBilinear_apply a _ _).symm)

omit [IsScalarTower ℝ ℂ V] in
theorem typeElevenBilinear_I_left (a : V [⋀^Fin 2]→L[ℝ] ℂ)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 1 1 a) (u v : V) :
    realCovectorBilinear a (Complex.I • u) v = -realCovectorBilinear a u (Complex.I • v) := by
  have h := typeElevenBilinear_I_I a ha u (Complex.I • v)
  simp only [smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg] at h
  linarith

end

/-! The Hermitian form determined by a real alternating form of type
(1,1), with imaginary part equal to the original alternating form. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

theorem complex_smul_real_imag (z : ℂ) (u : V) :
    z • u = z.re • u + z.im • (Complex.I • u) := by
  calc
    z • u = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • u := by rw [Complex.re_add_im]
    _ = (z.re : ℂ) • u + (z.im : ℂ) • (Complex.I • u) := by rw [add_smul, mul_smul]
    _ = _ := congrArg₂ (fun x y : V => x + y)
      (IsScalarTower.algebraMap_smul ℂ z.re u)
      (IsScalarTower.algebraMap_smul ℂ z.im (Complex.I • u))

def typeElevenHermitianValue (a : V [⋀^Fin 2]→L[ℝ] ℂ) (u v : V) : ℂ :=
  ⟨realCovectorBilinear a u (Complex.I • v), realCovectorBilinear a u v⟩

omit [IsScalarTower ℝ ℂ V] in
theorem typeElevenHermitianValue_add_left (a : V [⋀^Fin 2]→L[ℝ] ℂ) (u v w : V) :
    typeElevenHermitianValue a (u + v) w =
      typeElevenHermitianValue a u w + typeElevenHermitianValue a v w := by
  apply Complex.ext <;> simp [typeElevenHermitianValue]

omit [IsScalarTower ℝ ℂ V] in
theorem typeElevenHermitianValue_add_right (a : V [⋀^Fin 2]→L[ℝ] ℂ) (u v w : V) :
    typeElevenHermitianValue a u (v + w) =
      typeElevenHermitianValue a u v + typeElevenHermitianValue a u w := by
  apply Complex.ext <;> simp [typeElevenHermitianValue, smul_add]

theorem typeElevenHermitianValue_smul_left (a : V [⋀^Fin 2]→L[ℝ] ℂ)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 1 1 a) (z : ℂ) (u v : V) :
    typeElevenHermitianValue a (z • u) v = star z * typeElevenHermitianValue a u v := by
  rw [complex_smul_real_imag]
  apply Complex.ext <;>
    simp [typeElevenHermitianValue, map_add, map_smul,
      typeElevenBilinear_I_I a ha, typeElevenBilinear_I_left a ha,
      Complex.mul_re, Complex.mul_im]

theorem typeElevenHermitianValue_smul_right (a : V [⋀^Fin 2]→L[ℝ] ℂ)
    (z : ℂ) (u v : V) :
    typeElevenHermitianValue a u (z • v) = z * typeElevenHermitianValue a u v := by
  rw [complex_smul_real_imag]
  have hs : Complex.I • (z.re • v + z.im • (Complex.I • v)) =
      z.re • (Complex.I • v) - z.im • v := by
    rw [smul_add, smul_comm Complex.I z.re, smul_comm Complex.I z.im,
      smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_neg, sub_eq_add_neg]
  apply Complex.ext <;>
    simp [typeElevenHermitianValue, hs, map_add, map_sub, map_smul,
      Complex.mul_re, Complex.mul_im]

def typeElevenHermitian (a : V [⋀^Fin 2]→L[ℝ] ℂ) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 1 1 a) :
    V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ where
  toFun u := {
    toFun := typeElevenHermitianValue a u
    map_add' := typeElevenHermitianValue_add_right a u
    map_smul' := fun z v => typeElevenHermitianValue_smul_right a z u v }
  map_add' u v := by
    ext w
    exact typeElevenHermitianValue_add_left a u v w
  map_smul' z u := by
    ext v
    exact typeElevenHermitianValue_smul_left a ha z u v

theorem typeElevenHermitian_symmetry (a : V [⋀^Fin 2]→L[ℝ] ℂ)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 1 1 a) (u v : V) :
    typeElevenHermitian a ha v u = star (typeElevenHermitian a ha u v) := by
  apply Complex.ext
  · change realCovectorBilinear a v (Complex.I • u) = realCovectorBilinear a u (Complex.I • v)
    rw [realCovectorBilinear_skew a (Complex.I • u) v, typeElevenBilinear_I_left a ha, neg_neg]
  · exact realCovectorBilinear_skew a u v

theorem typeElevenHermitian_positive (a : V [⋀^Fin 2]→L[ℝ] ℂ)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 1 1 a)
    (hp : ∀ u : V, u ≠ 0 → 0 < (a ![u, Complex.I • u]).re)
    (u : V) (hu : u ≠ 0) : 0 < (typeElevenHermitian a ha u u).re := by
  change 0 < realCovectorBilinear a u (Complex.I • u)
  rw [realCovectorBilinear_apply]
  exact hp u hu

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TypeElevenBilinear

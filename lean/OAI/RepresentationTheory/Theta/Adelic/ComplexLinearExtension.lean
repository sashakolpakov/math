import Mathlib

/-! # Complex Linear Extension -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.ComplexLinearExtension

/-! Complex-linear extension of a real-linear map out of a coordinate
space, using the actual coordinate basis. -/

open scoped Classical

variable {I V : Type*} [Fintype I] [AddCommGroup V] [Module ℂ V]

def complexExtension (f : (I → ℝ) →ₗ[ℝ] V) : (I → ℂ) →ₗ[ℂ] V :=
  (Pi.basisFun ℂ I).constr ℂ (fun i => f (Pi.single i 1))

theorem complexExtension_apply (f : (I → ℝ) →ₗ[ℝ] V) (z : I → ℂ) :
    complexExtension f z = ∑ i, z i • f (Pi.single i 1) := by
  rw [complexExtension, Module.Basis.constr_apply]
  simp [Finsupp.sum_fintype]

theorem complexExtension_real (f : (I → ℝ) →ₗ[ℝ] V) (x : I → ℝ) :
    complexExtension f (fun i => (x i : ℂ)) = f x := by
  rw [complexExtension_apply]
  have h := congrArg f ((Pi.basisFun ℝ I).sum_repr x)
  simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, Complex.coe_smul] using h

theorem complexExtension_decomposition (f : (I → ℝ) →ₗ[ℝ] V) (z : I → ℂ) :
    complexExtension f z = f (fun i => (z i).re) + Complex.I • f (fun i => (z i).im) := by
  have hz : z = (fun i => ((z i).re : ℂ)) + Complex.I • (fun i => ((z i).im : ℂ)) := by
    funext i
    change z i = (z i).re + Complex.I * (z i).im
    rw [mul_comm]
    exact (Complex.re_add_im (z i)).symm
  conv_lhs => rw [hz, map_add, map_smul, complexExtension_real, complexExtension_real]

theorem complexExtension_unique (f : (I → ℝ) →ₗ[ℝ] V) (g : (I → ℂ) →ₗ[ℂ] V)
    (hg : ∀ x : I → ℝ, g (fun i => (x i : ℂ)) = f x) : g = complexExtension f := by
  apply (Pi.basisFun ℂ I).ext
  intro i
  have hi : (Pi.basisFun ℂ I) i = fun j => (((Pi.single i (1 : ℝ) : I → ℝ) j) : ℂ) := by
    funext j
    simp [Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> norm_num
  rw [hi, hg, complexExtension_real]

end RepresentationTheory.Theta.Adelic.ComplexLinearExtension

namespace RepresentationTheory.Theta.Adelic.ComplexLinearExtension.PairedComplexification

/-! Complexifying a real coordinate space identified with a complex
vector space gives the standard and conjugate summands. -/

open scoped Classical ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.ComplexLinearExtension
variable {I J : Type*} [Fintype I]

def conjugateVector : (J → ℂ) ≃ₗ[ℝ] (J → ℂ) :=
  LinearEquiv.piCongrRight (fun _ => Complex.conjAe.toLinearEquiv)

variable (e : (I → ℝ) ≃ₗ[ℝ] (J → ℂ))

def pairedRealMap : (I → ℝ) →ₗ[ℝ] ((J → ℂ) × (J → ℂ)) :=
  e.toLinearMap.prod ((conjugateVector.toLinearMap).comp e.toLinearMap)

def pairedComplexMap : (I → ℂ) →ₗ[ℂ] ((J → ℂ) × (J → ℂ)) :=
  complexExtension (pairedRealMap e)

theorem pairedComplexMap_real (x : I → ℝ) :
    pairedComplexMap e (fun i => (x i : ℂ)) = (e x, fun j => conj (e x j)) :=
  complexExtension_real (pairedRealMap e) x

theorem pairedComplexMap_first (z : I → ℂ) (j : J) :
    (pairedComplexMap e z).1 j =
      e (fun i => (z i).re) j + Complex.I * e (fun i => (z i).im) j := by
  exact congrArg (fun p : (J → ℂ) × (J → ℂ) => p.1 j)
    (complexExtension_decomposition (pairedRealMap e) z)

theorem pairedComplexMap_second (z : I → ℂ) (j : J) :
    (pairedComplexMap e z).2 j =
      conj (e (fun i => (z i).re) j) + Complex.I * conj (e (fun i => (z i).im) j) := by
  exact congrArg (fun p : (J → ℂ) × (J → ℂ) => p.2 j)
    (complexExtension_decomposition (pairedRealMap e) z)

theorem pairedComplexMap_injective : Function.Injective (pairedComplexMap e) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  have hu (j : J) : e (fun i => (z i).re) j = 0 ∧ e (fun i => (z i).im) j = 0 := by
    have h₁ := congrArg (fun p : (J → ℂ) × (J → ℂ) => p.1 j) hz
    have h₂ := congrArg (fun p : (J → ℂ) × (J → ℂ) => conj (p.2 j)) hz
    rw [pairedComplexMap_first] at h₁
    rw [pairedComplexMap_second] at h₂
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_add, map_mul,
      Complex.conj_I, Complex.conj_conj, map_zero, neg_mul] at h₁ h₂
    constructor
    · linear_combination (h₁ + h₂) / 2
    · have hi : Complex.I * e (fun i => (z i).im) j = 0 := by
        linear_combination (h₁ - h₂) / 2
      exact (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
  have hr : (fun i => (z i).re) = 0 := e.injective (by
    rw [map_zero]
    funext j
    exact (hu j).1)
  have hi : (fun i => (z i).im) = 0 := e.injective (by
    rw [map_zero]
    funext j
    exact (hu j).2)
  funext i
  apply Complex.ext
  · exact congrFun hr i
  · exact congrFun hi i

theorem pairedComplexMap_surjective : Function.Surjective (pairedComplexMap e) := by
  rintro ⟨x, y⟩
  let u : J → ℂ := fun j => (x j + conj (y j)) / 2
  let v : J → ℂ := fun j => -Complex.I * (x j - conj (y j)) / 2
  let a := e.symm u
  let b := e.symm v
  refine ⟨(fun i => (a i : ℂ)) + Complex.I • (fun i => (b i : ℂ)), ?_⟩
  rw [map_add, map_smul, pairedComplexMap_real, pairedComplexMap_real]
  change (e (e.symm u), fun j => conj (e (e.symm u) j)) +
    Complex.I • (e (e.symm v), fun j => conj (e (e.symm v) j)) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext j
    change u j + Complex.I * v j = x j
    dsimp [u, v]
    linear_combination -(x j - conj (y j)) / 2 * Complex.I_mul_I
  · funext j
    change conj (u j) + Complex.I * conj (v j) = y j
    simp only [u, v, map_div₀, map_add, map_sub, map_neg, map_mul,
      Complex.conj_I, Complex.conj_conj, map_ofNat, neg_neg]
    linear_combination (conj (x j) - y j) / 2 * Complex.I_mul_I

def pairedComplexEquiv : (I → ℂ) ≃ₗ[ℂ] ((J → ℂ) × (J → ℂ)) :=
  LinearEquiv.ofBijective (pairedComplexMap e)
    ⟨pairedComplexMap_injective e, pairedComplexMap_surjective e⟩

end RepresentationTheory.Theta.Adelic.ComplexLinearExtension.PairedComplexification

end

end OAI

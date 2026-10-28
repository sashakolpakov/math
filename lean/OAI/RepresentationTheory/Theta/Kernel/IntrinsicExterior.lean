import Mathlib

/-! # Intrinsic Exterior -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

noncomputable section

/-! Ordinary complex top covectors on the two-ball, with their literal
alternating evaluation and wedge product. No theta or descent input. -/

open scoped Classical _root_.Matrix

abbrev Tangent := Fin 2 → ℂ
abbrev Cotangent := Tangent →L[ℂ] ℂ
abbrev TopCovector := Tangent [⋀^Fin 2]→L[ℂ] ℂ

def area : TopCovector where
  toAlternatingMap := Matrix.detRowAlternating
  cont := by
    change Continuous (Matrix.det : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    have hd : (Matrix.det : Matrix (Fin 2) (Fin 2) ℂ → ℂ) =
        fun M => M 0 0 * M 1 1 - M 0 1 * M 1 0 := funext Matrix.det_fin_two
    rw [hd]
    fun_prop

theorem area_apply (u v : Tangent) : area ![u, v] = u 0 * v 1 - u 1 * v 0 := by
  change Matrix.det ![u, v] = _
  exact Matrix.det_fin_two _

def wedgeCoefficient (a b : Cotangent) : ℂ :=
  a ![1, 0] * b ![0, 1] - a ![0, 1] * b ![1, 0]

def wedge (a b : Cotangent) : TopCovector := wedgeCoefficient a b • area

theorem covector_coordinates (a : Cotangent) (u : Tangent) :
    a u = u 0 * a ![1, 0] + u 1 * a ![0, 1] := by
  have hu : u = u 0 • ![1, 0] + u 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp
  calc
    a u = a (u 0 • ![1, 0] + u 1 • ![0, 1]) := congrArg a hu
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

theorem wedge_apply (a b : Cotangent) (u v : Tangent) :
    wedge a b ![u, v] = a u * b v - a v * b u := by
  simp only [wedge, ContinuousAlternatingMap.smul_apply, smul_eq_mul, area_apply,
    wedgeCoefficient, covector_coordinates a u, covector_coordinates a v,
    covector_coordinates b u, covector_coordinates b v]
  ring

theorem wedgeCoefficient_add_left (a b c : Cotangent) :
    wedgeCoefficient (a + b) c = wedgeCoefficient a c + wedgeCoefficient b c := by
  simp only [wedgeCoefficient, _root_.add_apply]
  ring

theorem wedgeCoefficient_smul_left (c : ℂ) (a b : Cotangent) :
    wedgeCoefficient (c • a) b = c * wedgeCoefficient a b := by
  simp only [wedgeCoefficient, _root_.smul_apply, smul_eq_mul]
  ring

theorem wedgeCoefficient_add_right (a b c : Cotangent) :
    wedgeCoefficient a (b + c) = wedgeCoefficient a b + wedgeCoefficient a c := by
  simp only [wedgeCoefficient, _root_.add_apply]
  ring

theorem wedgeCoefficient_smul_right (c : ℂ) (a b : Cotangent) :
    wedgeCoefficient a (c • b) = c * wedgeCoefficient a b := by
  simp only [wedgeCoefficient, _root_.smul_apply, smul_eq_mul]
  ring

theorem wedge_naturality (a b : Cotangent) (g : Tangent →L[ℂ] Tangent) :
    (wedge a b).compContinuousLinearMap g = wedge (a.comp g) (b.comp g) := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change wedge a b ![g (v 0), g (v 1)] = wedge (a.comp g) (b.comp g) ![v 0, v 1]
  simp only [wedge_apply, ContinuousLinearMap.comp_apply]

theorem spanning_wedge_nonzero {I J : Type*} (a : I → Cotangent) (b : J → Cotangent)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (hb : Submodule.span ℂ (Set.range b) = ⊤) :
    ∃ i j, wedge (a i) (b j) ≠ 0 := by
  by_contra! h
  have hzero : ∀ i j, wedgeCoefficient (a i) (b j) = 0 := by
    intro i j
    have he := congrArg (fun ω : TopCovector => ω ![![1, 0], ![0, 1]]) (h i j)
    simpa [wedge, area_apply] using he
  have hallLeft : ∀ x ∈ Submodule.span ℂ (Set.range a), ∀ j, wedgeCoefficient x (b j) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hzero i
    | zero => intro j; simp [wedgeCoefficient]
    | add x y _ _ hx hy => intro j; rw [wedgeCoefficient_add_left, hx, hy, add_zero]
    | smul c x _ hx => intro j; rw [wedgeCoefficient_smul_left, hx, mul_zero]
  have hall : ∀ x y : Cotangent, wedgeCoefficient x y = 0 := by
    intro x y
    have hy : y ∈ Submodule.span ℂ (Set.range b) := by rw [hb]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact hallLeft x (by rw [ha]; trivial) j
    | zero => simp [wedgeCoefficient]
    | add y z _ _ hy hz => rw [wedgeCoefficient_add_right, hy, hz, add_zero]
    | smul c y _ hy => rw [wedgeCoefficient_smul_right, hy, mul_zero]
  have he := hall (ContinuousLinearMap.proj 0) (ContinuousLinearMap.proj 1)
  norm_num [wedgeCoefficient] at he

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Totally Real Data -/

namespace OAI.RepresentationTheory.Theta.Adelic.TotallyRealData

noncomputable section

/-! The arithmetic ball data imply that the base number field is
totally real and that its degree is the number of displayed real places. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData _root_.NumberField

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem displayed_place_real (i : Fin A.places) : (A.enumerate i).IsReal := by
  by_contra hi
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp hi)
  let f : ℂ ≃+* ℝ := e.symm.trans (A.real i)
  have h : f Complex.I * f Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  nlinarith [sq_nonneg (f Complex.I)]

include A in
theorem arithmetic_totally_real : NumberField.IsTotallyReal F := by
  constructor
  intro v
  obtain ⟨i, rfl⟩ := A.enumerate.surjective v
  exact displayed_place_real A i

theorem degree_eq_places : Module.finrank ℚ F = A.places := by
  let : NumberField.IsTotallyReal F := arithmetic_totally_real A
  have hc := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero] at hc
  have he := Fintype.card_congr A.enumerate
  rw [Fintype.card_fin] at he
  exact (NumberField.IsTotallyReal.finrank (K := F)).trans (hc.symm.trans he.symm)

end

end OAI.RepresentationTheory.Theta.Adelic.TotallyRealData

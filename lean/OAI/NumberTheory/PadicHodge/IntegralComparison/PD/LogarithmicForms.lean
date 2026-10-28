import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.Logarithm

/-! # Logarithmic Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicForms

noncomputable section

/-! Logarithmic differentials in the original PD de Rham complex.
Congruent units have cohomologous closed logarithmic forms whenever
the residue characteristic is nilpotent. The primitive is an explicit
finite divided-power logarithm. -/

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

def zeroForm (a : A) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ 0 :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a (fun i : Fin 0 => i.elim0)

theorem differential_zeroForm (a : A) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ 0 (zeroForm R A I δ a) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A I δ a := by
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.projectedDifferential R A I δ 0
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (fun i : Fin 0 => i.elim0)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.projectedDifferential_symbol, AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D_apply]
  congr 1
  ext i
  fin_cases i
  rfl

def dlog (u : Aˣ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ 1 :=
  Logarithm.dlog (AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A I δ) u

theorem dlog_symbol (u : Aˣ) : dlog R A I δ u =
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ (↑u⁻¹ : A) (fun _ : Fin 1 => (u : A)) := by
  rw [dlog, Logarithm.dlog, AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D_apply,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_smul_one R A I δ (↑u⁻¹ : A)]

theorem dlog_closed (u : Aˣ) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ 1 (dlog R A I δ u) = 0 := by
  rw [dlog_symbol]
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.projectedDifferential R A I δ 1
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A (↑u⁻¹ : A) (fun _ : Fin 1 => (u : A))) = 0
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.projectedDifferential_symbol]
  have h := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_cons_mul R A I δ (u : A) (↑u⁻¹ : A)
    (fun _ : Fin 1 => (u : A))
  have halt : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ 1
      (Fin.cons (u : A) (fun _ : Fin 1 => (u : A))) = 0 :=
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_alt R A I δ _ 0 1 rfl (by decide)
  rw [Units.mul_inv, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_cons_one, halt, smul_zero, add_zero] at h
  have he := congrArg (fun ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ 2 => (↑u⁻¹ : A) • ω) h
  simpa only [smul_zero, smul_smul, Units.inv_mul, one_smul] using he.symm

theorem congruent_units_exact (p r : ℕ) (hp : 0 < p) (hpr : (p : A) ^ r = 0)
    (u v : Aˣ) (huv : (v : A) - (u : A) ∈ I) :
    ∃ η : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ 0,
      dlog R A I δ v - dlog R A I δ u = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ 0 η := by
  obtain ⟨b, hb⟩ := DividedPower.Nilpotence.pow_dvd_mul_factorial p r hp
  have hf : ((r * p).factorial : A) = 0 := by
    rw [hb, Nat.cast_mul, Nat.cast_pow, hpr, zero_mul]
  have hx : (↑(v * u⁻¹) : A) - 1 ∈ I := by
    have he : (↑(v * u⁻¹) : A) - 1 = ((v : A) - (u : A)) * ↑u⁻¹ := by
      rw [Units.val_mul, sub_mul, Units.mul_inv]
    rw [he]
    exact I.mul_mem_right _ huv
  refine ⟨zeroForm R A I δ
    (Logarithm.logarithm I δ (r * p) ((↑(v * u⁻¹) : A) - 1)), ?_⟩
  rw [differential_zeroForm]
  exact Logarithm.dlog_sub_exact I δ (AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A I δ)
    (r * p) u v hx hf (fun j => AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D_dpow R A I δ j hx)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicForms

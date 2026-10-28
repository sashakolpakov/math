import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Forms

/-! # One Form Realization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OneFormRealization

noncomputable section

/-! Universal realization of the constructed degree-one algebraic forms by
a derivation, with the degree-zero differential compatibility proved. -/

universe u v

variable {A : Type u} [CommRing A] [Algebra ℂ A]
  {M : Type v} [AddCommGroup M] [Module A M] [Module ℂ M]
  [IsScalarTower ℂ A M] [SMulCommClass A ℂ M]
  (D : Derivation ℂ A M)

def rawOneFormRealization : Algebraic.Forms.RawForm A 1 →ₗ[ℂ] M :=
  Finsupp.linearCombination ℂ (fun a : Fin 2 → A => a 0 • D (a 1))

omit [IsScalarTower ℂ A M] [SMulCommClass A ℂ M] in
@[simp]
theorem rawOneFormRealization_symbol (a : Fin 2 → A) :
    rawOneFormRealization D (Algebraic.Forms.symbol A a) = a 0 • D (a 1) := by
  simp [rawOneFormRealization, Algebraic.Forms.symbol]

omit [IsScalarTower ℂ A M] [SMulCommClass A ℂ M] in
theorem rawOneFormRealization_d0 (r : Algebraic.Forms.RawForm A 0) :
    rawOneFormRealization D (Algebraic.Forms.rawDifferential A 0 r) = D (Algebraic.Forms.rawZeroEvaluation A r) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single a c =>
      simp [rawOneFormRealization, Algebraic.Forms.rawDifferential, Algebraic.Forms.rawZeroEvaluation]

theorem oneFormRelation_realization_zero {r : Algebraic.Forms.RawForm A 1} (hr : Algebraic.Forms.FormRelation A 1 r) :
    rawOneFormRealization D r = 0 := by
  cases hr with
  | add n a i x y =>
      fin_cases i <;>
        simp [map_sub, rawOneFormRealization_symbol, map_add, add_smul, smul_add]
  | smul n a i c x =>
      fin_cases i
      · simp [map_sub, rawOneFormRealization_symbol, map_smul, smul_assoc]
      · simp [map_sub, rawOneFormRealization_symbol, map_smul, smul_comm (a 0) c]
  | leibniz n a i x y =>
      have hi : i = 0 := Fin.eq_zero i
      simp [hi, map_sub, rawOneFormRealization_symbol, D.leibniz, smul_add, mul_smul]
  | constant n a i c =>
      have hi : i = 0 := Fin.eq_zero i
      simp [hi, rawOneFormRealization_symbol, D.map_algebraMap]
  | alternating n a i j hij ha =>
      exact False.elim (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm))
  | differential hr =>
      rw [rawOneFormRealization_d0, Algebraic.Forms.zeroRelation_evaluates_zero A hr, map_zero]

/-- The map a db ↦ a • D b, descended through every defining relation. -/
def oneFormRealization : Algebraic.Forms.Form A 1 →ₗ[ℂ] M :=
  (Algebraic.Forms.relations A 1).liftQ (rawOneFormRealization D)
    (Submodule.span_le.mpr (fun _ hr => oneFormRelation_realization_zero D hr))

@[simp]
theorem oneFormRealization_symbol (a : Fin 2 → A) :
    oneFormRealization D (Algebraic.Forms.formSymbol A a) = a 0 • D (a 1) :=
  rawOneFormRealization_symbol D a

/-- Differentiating an algebraic zero-form then realizing agrees with D. -/
theorem oneFormRealization_d0 (a : Algebraic.Forms.Form A 0) :
    oneFormRealization D (Algebraic.Forms.differential A 0 a) = D (Algebraic.Forms.zeroEvaluation A a) := by
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations A 0).mkQ_surjective a
  exact rawOneFormRealization_d0 D r

theorem oneFormRealization_unique (φ : Algebraic.Forms.Form A 1 →ₗ[ℂ] M)
    (hφ : ∀ a : Fin 2 → A, φ (Algebraic.Forms.formSymbol A a) = a 0 • D (a 1)) :
    φ = oneFormRealization D := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations A 1).mkQ_surjective x
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single a c =>
      have hc : Finsupp.single a c = c • Algebraic.Forms.symbol A a := by simp [Algebraic.Forms.symbol]
      rw [hc]
      simp only [map_smul]
      exact congrArg (c • ·) ((hφ a).trans (oneFormRealization_symbol D a).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.OneFormRealization

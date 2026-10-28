import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyParameterValuesBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramCrudeBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


def base (x : Input) : ℕ := magnitude x+16*(2*magnitude x+1)^2+128

theorem initial_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (Layout.initialModel x l).val j ≤ base x := by
  intro j
  dsimp [Layout.initialModel,Layout.initialValues,base,magnitude]
  split <;> omega

theorem grid_le (x : Input) (l : Fin 8 → ℕ) :
    (Layout.model x l).val 31 ≤ base x := by
  rw [(Layout.model_core_values x l).2.2.2.2.2.2.2]
  have hg := Asymptotic.layout_grid_square x.freeCount
  have hr : 1 ≤ Asymptotic.layoutR x.freeCount := by
    dsimp [Asymptotic.layoutR]; omega
  have hp : Asymptotic.layoutR x.freeCount^(2*Asymptotic.layoutQ x.freeCount) ≤
      (Asymptotic.layoutR x.freeCount^(4*Asymptotic.layoutQ x.freeCount))^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hr (by omega)
  change Asymptotic.layoutR x.freeCount^(2*Asymptotic.layoutQ x.freeCount) ≤ base x
  have hb : x.freeCount+16 ≤ base x := by dsimp [base,magnitude]; omega
  exact hp.trans (hg.trans hb)

theorem log_field_le (Q : ℕ) : 3^(Nat.log2 Q+2) ≤ 16*(Q+1)^2 := by
  have hlog : 2^Nat.log2 Q ≤ Q+1 := by
    by_cases hQ : Q=0
    · subst Q; norm_num
    · exact (Nat.log2_self_le hQ).trans (by omega)
  have hp : 2^(Nat.log2 Q+2) ≤ 4*(Q+1) := by
    rw [pow_add]
    norm_num
    omega
  calc
    _  ≤  4^(Nat.log2 Q+2) := Nat.pow_le_pow_left (by decide) _
    _ = (2^(Nat.log2 Q+2))^2 := by
      rw [← pow_mul,Nat.mul_comm,pow_mul]
      norm_num
    _  ≤  (4*(Q+1))^2 := Nat.pow_le_pow_left hp _
    _ = _ := by ring

theorem field_le (x : Input) (l : Fin 8 → ℕ) :
    (Layout.model x l).val 35 ≤ base x := by
  have he : (Layout.model x l).val 35=
      3^(Nat.log2 ((Layout.model x l).val 21)+2) := by
    simp [Layout.model, Layout.code, Layout.coreCode, Layout.prefixCode,
      Layout.earlyCode, Layout.quotientCode, Layout.finishCode, Layout.heavyCode,
      Layout.powerCode, Layout.tailCode, result, next, value, output,
      Layout.initialModel, Layout.initialValues, BinaryArithmetic.toNat,
      BinaryArithmetic.bitVal]
  rw [he,(Layout.model_core_values x l).2.2.2.2.1]
  have hQ : (produce x).Q ≤ 2*magnitude x :=
    (Nat.div_le_self _ _).trans (L_le_magnitude x)
  have hh : 16*((produce x).Q+1)^2 ≤ 16*(2*magnitude x+1)^2 := by
    gcongr
  exact (log_field_le _).trans (hh.trans (by dsimp [base]; omega))

theorem layout_powers (x : Input) (l : Fin 8 → ℕ) :
    PowerBounds (base x) Layout.code (Layout.initialModel x l) := by
  simp [Layout.code, Layout.coreCode, Layout.prefixCode, Layout.earlyCode,
    Layout.quotientCode, Layout.finishCode, Layout.heavyCode, Layout.powerCode,
    Layout.tailCode, PowerBounds, PowerBound, next, value, output]
  constructor
  · simpa [Layout.model, Layout.code, Layout.coreCode, Layout.prefixCode,
      Layout.earlyCode, Layout.quotientCode, Layout.finishCode, Layout.heavyCode,
      Layout.powerCode, Layout.tailCode, result, next, value, output] using grid_le x l
  · simpa [Layout.model, Layout.code, Layout.coreCode, Layout.prefixCode,
      Layout.earlyCode, Layout.quotientCode, Layout.finishCode, Layout.heavyCode,
      Layout.powerCode, Layout.tailCode, result, next, value, output] using field_le x l

theorem layout_constants : ∀ i ∈ Layout.code,Constants i := by
  simp [Layout.code, Layout.coreCode, Layout.prefixCode, Layout.earlyCode,
    Layout.quotientCode, Layout.finishCode, Layout.heavyCode, Layout.powerCode,
    Layout.tailCode, Constants, BinaryArithmetic.bitVal]

theorem guard_constants : ∀ i ∈ GuardSetup.code,Constants i := by
  simp [GuardSetup.code, GuardSetup.preparation, GuardSetup.emissions,
    Constants, BinaryArithmetic.bitVal]

theorem guard_powers (B : ℕ) (m : Model) : PowerBounds B GuardSetup.code m := by
  simp [GuardSetup.code, GuardSetup.preparation, GuardSetup.emissions,
    PowerBounds, PowerBound]

theorem layout_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (Layout.model x l).val j ≤ iter Layout.code.length (base x) :=
  result_le le_rfl _ _ (initial_le x l) layout_constants (layout_powers x l)

theorem prepared_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (Prepared.finalModel x l).val j ≤
      iter GuardSetup.code.length (iter Layout.code.length (base x)) :=
  result_le le_rfl _ _ (layout_le x l) guard_constants (guard_powers _ _)

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms

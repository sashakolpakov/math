import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding

/-! # Theta Divided Powers -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaDividedPowers

noncomputable section

/-! An integral spanning description of the actual crystalline envelope. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope
variable (p : ℕ) [Fact p.Prime]

def gammaXi (n : ℕ) : Logarithm.PeriodRings.AInfFractionField p :=
  algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) (ThetaKernel.thetaGenerator p) ^ n / n.factorial

theorem gammaXi_zero : gammaXi p 0 = 1 := by simp [gammaXi]

theorem gammaXi_mul (m n : ℕ) : gammaXi p m * gammaXi p n =
    ((m + n).choose m : Logarithm.PeriodRings.AInfFractionField p) * gammaXi p (m + n) := by
  classical
  have h := (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (Logarithm.PeriodRings.AInfFractionField p))).mul_dpow
    (m := m) (n := n)
    (x := algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) (ThetaKernel.thetaGenerator p)) (by simp)
  simpa only [DividedPowers.RatAlgebra.dpow_apply, Submodule.mem_top, ite_eq_left,
    Ring.inverse_eq_inv', gammaXi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

def thetaDividedPower (n : ℕ) : Logarithm.PeriodRings.ACrisUncompleted p :=
  Logarithm.PeriodRings.dividedPower p (ThetaKernel.thetaGenerator p) n (by
    rw [Logarithm.PeriodRings.thetaModP, RingHom.comp_apply, ThetaKernel.thetaGenerator_theta, map_zero])

theorem thetaDividedPower_coe (n : ℕ) :
    (thetaDividedPower p n : Logarithm.PeriodRings.AInfFractionField p) = gammaXi p n := rfl

def xiSpan : Submodule (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) :=
  Submodule.span (Logarithm.PeriodRings.AInf p) (Set.range (gammaXi p))

theorem gammaXi_mem (n : ℕ) : gammaXi p n ∈ xiSpan p :=
  Submodule.subset_span ⟨n, rfl⟩

theorem xiSpan_one : (1 : Logarithm.PeriodRings.AInfFractionField p) ∈ xiSpan p := by
  rw [← gammaXi_zero p]
  exact gammaXi_mem p 0

theorem xiSpan_mul {x y : Logarithm.PeriodRings.AInfFractionField p} (hx : x ∈ xiSpan p)
    (hy : y ∈ xiSpan p) : x * y ∈ xiSpan p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      rw [gammaXi_mul]
      simpa only [Algebra.smul_def, map_natCast] using
        (xiSpan p).smul_mem ((m + n).choose m : Logarithm.PeriodRings.AInf p) (gammaXi_mem p (m + n))
    | zero => simp
    | add y z _ _ hy hz => simpa only [mul_add] using (xiSpan p).add_mem hy hz
    | smul a y _ hy =>
      simpa only [mul_smul_comm] using (xiSpan p).smul_mem a hy
  | zero => simp
  | add x z _ _ hx hz => simpa only [add_mul] using (xiSpan p).add_mem hx hz
  | smul a x _ hx => simpa only [smul_mul_assoc] using (xiSpan p).smul_mem a hx

def xiSpanAlgebra : Subalgebra (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) where
  carrier := xiSpan p
  zero_mem' := (xiSpan p).zero_mem
  one_mem' := xiSpan_one p
  add_mem' := (xiSpan p).add_mem
  mul_mem' := xiSpan_mul p
  algebraMap_mem' a := by
    change algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) a ∈ xiSpan p
    simpa only [Algebra.smul_def, mul_one] using (xiSpan p).smul_mem a (xiSpan_one p)

/-- Every element of the envelope is an integral linear combination of xi^n/n!. -/
theorem uncompleted_mem_xiSpan (x : Logarithm.PeriodRings.ACrisUncompleted p) :
    (x : Logarithm.PeriodRings.AInfFractionField p) ∈ xiSpan p := by
  have hle : Logarithm.PeriodRings.aCrisUncompleted p ≤ xiSpanAlgebra p := by
    rw [DeRhamEnvelope.uncompletedEnvelope_eq]
    apply Algebra.adjoin_le
    rintro _ ⟨⟨n, x⟩, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
      (show (x : Logarithm.PeriodRings.AInf p) ∈ Ideal.span {ThetaKernel.thetaGenerator p} from
        ThetaKernel.theta_kernel_eq_span p ▸ x.property)
    change algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) (x : Logarithm.PeriodRings.AInf p) ^ n /
      (n.factorial : Logarithm.PeriodRings.AInfFractionField p) ∈ xiSpan p
    rw [ha, map_mul, mul_pow]
    have he : (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) (ThetaKernel.thetaGenerator p) ^ n *
        algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) a ^ n) / (n.factorial : Logarithm.PeriodRings.AInfFractionField p) =
        a ^ n • gammaXi p n := by
      simp only [Algebra.smul_def, map_pow, gammaXi]
      ring
    rw [he]
    exact (xiSpan p).smul_mem _ (gammaXi_mem p n)
  exact hle x.property

theorem uncompleted_mem_span (x : Logarithm.PeriodRings.ACrisUncompleted p) :
    x ∈ Submodule.span (Logarithm.PeriodRings.AInf p) (Set.range (thetaDividedPower p)) := by
  have hs : (Submodule.span (Logarithm.PeriodRings.AInf p) (Set.range (thetaDividedPower p))).map
      (Logarithm.PeriodRings.aCrisUncompleted p).val.toLinearMap = xiSpan p := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp (hs.symm ▸ uncompleted_mem_xiSpan p x)
  exact (Subtype.ext he : y = x) ▸ hy

theorem thetaDividedPower_integral_mul (n : ℕ) :
    (p : Logarithm.PeriodRings.ACrisUncompleted p) ^ n * thetaDividedPower p n =
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p)
        (PeriodInvariants.AdicEstimates.Frobenius.pDividedPowerCoefficient p n * ThetaKernel.thetaGenerator p ^ n) := by
  apply Subtype.ext
  change (p : Logarithm.PeriodRings.AInfFractionField p) ^ n * gammaXi p n =
    algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p)
      (PeriodInvariants.AdicEstimates.Frobenius.pDividedPowerCoefficient p n * ThetaKernel.thetaGenerator p ^ n)
  rw [map_mul, map_pow, PeriodInvariants.AdicEstimates.Frobenius.pDividedPowerCoefficient_fraction, gammaXi]
  ring

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaDividedPowers

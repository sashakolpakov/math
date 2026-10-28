import OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittFinite
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients

/-! # Coefficient Finiteness -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFiniteness

noncomputable section

/-! Finite-dimensional p-adic structures on the constructed Witt coefficient fields. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittFinite OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients
variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k] [CharP k p]

omit [Fintype k] in
theorem padicToWitt_injective : Function.Injective (WittFinite.padicToWitt p k) :=
  (WittVector.map_injective _ (ZMod.castHom (dvd_refl p) k).injective).comp
    (WittVector.equiv p).symm.injective

def padicIntegerToCoefficient : ℤ_[p] →+* UnramifiedCoefficients.CoefficientField (p := p) (k := k) :=
  (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k))).comp (WittFinite.padicToWitt p k)

instance integerAlgebra : Algebra ℤ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :=
  (padicIntegerToCoefficient p k).toAlgebra

instance integerSMul : SMul ℤ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :=
  ⟨fun a x => padicIntegerToCoefficient p k a * x⟩

instance integerModule : Module ℤ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) := Algebra.toModule

instance wittSMul : SMul (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :=
  (inferInstance : Algebra (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k))).toSMul

instance wittModule : Module (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) := Algebra.toModule

instance integerWittTower : IsScalarTower ℤ_[p] (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :=
  IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := WittVector p k)
    (A := UnramifiedCoefficients.CoefficientField (p := p) (k := k)) fun _ => rfl

omit [Fintype k] in
theorem padicIntegerToCoefficient_injective : Function.Injective (padicIntegerToCoefficient p k) :=
  (IsFractionRing.injective (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k))).comp
    (padicToWitt_injective p k)

def padicToCoefficient : ℚ_[p] →+* UnramifiedCoefficients.CoefficientField (p := p) (k := k) :=
  IsFractionRing.lift (padicIntegerToCoefficient_injective p k)

instance padicAlgebra : Algebra ℚ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :=
  (padicToCoefficient p k).toAlgebra

instance padicModule : Module ℚ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) := Algebra.toModule

omit [Fintype k] in
theorem padicToCoefficient_integer (a : ℤ_[p]) :
    padicToCoefficient p k (algebraMap ℤ_[p] ℚ_[p] a) = padicIntegerToCoefficient p k a :=
  IsFractionRing.lift_algebraMap (padicIntegerToCoefficient_injective p k) a

instance integerPadicTower : IsScalarTower ℤ_[p] ℚ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :=
  IsScalarTower.of_algebraMap_eq fun a => (padicToCoefficient_integer p k a).symm

omit [Fintype k] in
theorem coefficientDenominators_le :
    Algebra.algebraMapSubmonoid (WittVector p k) (nonZeroDivisors ℤ_[p]) ≤
      nonZeroDivisors (WittVector p k) := by
  rintro x ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp ha)
    ((padicToWitt_injective p k) (h.trans (map_zero _).symm))

theorem coefficientDenominators_cofinal (x : WittVector p k)
    (hx : x ∈ nonZeroDivisors (WittVector p k)) :
    ∃ y ∈ Algebra.algebraMapSubmonoid (WittVector p k) (nonZeroDivisors ℤ_[p]), x ∣ y := by
  obtain ⟨n, u, hu⟩ := WittVector.exists_eq_pow_p_mul' x (mem_nonZeroDivisors_iff_ne_zero.mp hx)
  refine ⟨(p : WittVector p k) ^ n, ?_, ?_⟩
  · refine ⟨(p : ℤ_[p]) ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ (NeZero.ne _)), ?_⟩
    simp only [map_pow, map_natCast]
  · rw [hu]
    exact ⟨↑u⁻¹, by simp only [mul_assoc, Units.mul_inv, mul_one]⟩

instance coefficientLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (WittVector p k) (nonZeroDivisors ℤ_[p]))
      (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :=
  (IsLocalization.iff_of_le_of_exists_dvd _ (nonZeroDivisors (WittVector p k))
    (coefficientDenominators_le p k) (coefficientDenominators_cofinal p k)).mpr inferInstance

instance coefficientFinite : Module.Finite ℚ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :=
  Module.Finite.of_isLocalization ℤ_[p] (WittVector p k) (nonZeroDivisors ℤ_[p])

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFiniteness

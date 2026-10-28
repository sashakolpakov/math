import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters

/-! # Coefficient Occurrence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientOccurrence.Spectral

noncomputable section

/-! A coefficient-field equivalence transports every simultaneous
generalized eigencondition on the same rational vector space. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

variable {F G U : Type*} [Field F] [Field G] [Algebra ℚ F] [Algebra ℚ G]
  [AddCommGroup U] [Module ℚ U]

def coefficientEquiv (e : F ≃ₐ[ℚ] G) : F ⊗[ℚ] U ≃ₗ[ℚ] G ⊗[ℚ] U :=
  TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl ℚ U)

theorem coefficientEquiv_smul (e : F ≃ₐ[ℚ] G) (c : F) (x : F ⊗[ℚ] U) :
    coefficientEquiv e (c • x) = e c • coefficientEquiv e x := by
  induction x using TensorProduct.inductionOn with
  | tmul a u =>
    change e (c * a) ⊗ₜ[ℚ] u = (e c * e a) ⊗ₜ[ℚ] u
    rw [map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem coefficientEquiv_baseChange (e : F ≃ₐ[ℚ] G) (T : Module.End ℚ U)
    (x : F ⊗[ℚ] U) :
    coefficientEquiv e (T.baseChange F x) = T.baseChange G (coefficientEquiv e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c u => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coefficientEquiv_shift_power (e : F ≃ₐ[ℚ] G) (T : Module.End ℚ U)
    (a : F) (n : ℕ) (x : F ⊗[ℚ] U) :
    coefficientEquiv e (((T.baseChange F - a • 1) ^ n) x) =
      ((T.baseChange G - e a • 1) ^ n) (coefficientEquiv e x) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n hn =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub,
      coefficientEquiv_baseChange, coefficientEquiv_smul, hn]

theorem coefficientEquiv_jointSpace {J : Type*} (e : F ≃ₐ[ℚ] G)
    (T : J → Module.End ℚ U) (χ : J → F) {x : F ⊗[ℚ] U}
    (hx : x ∈ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange F) χ) :
    coefficientEquiv e x ∈ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange G) (fun h => e (χ h)) := by
  simp only [HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace, Submodule.mem_iInf] at hx ⊢
  intro h
  obtain ⟨n, hn, hx⟩ := Module.End.mem_genEigenspace.mp (hx h)
  refine Module.End.mem_genEigenspace.mpr ⟨n, hn, ?_⟩
  change (((T h).baseChange G - e (χ h) • 1) ^ n) (coefficientEquiv e x) = 0
  rw [← coefficientEquiv_shift_power, LinearMap.mem_ker.mp hx, map_zero]

theorem coefficientEquiv_occurrence {J : Type*} (e : F ≃ₐ[ℚ] G)
    (T : J → Module.End ℚ U) (χ : J → F)
    (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange F) χ ≠ ⊥) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange G) (fun h => e (χ h)) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  apply (Submodule.ne_bot_iff _).mpr
  exact ⟨coefficientEquiv e x, coefficientEquiv_jointSpace e T χ hx,
    fun hz => hx0 ((coefficientEquiv e).injective (hz.trans (map_zero _).symm))⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientOccurrence.Spectral

import OAI.RepresentationTheory.Weil.UnitarySplitting.RealChartTestSpace
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier

/-! # Heisenberg Stability -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.HeisenbergStability.Construction

noncomputable section

/-! Weyl operators preserve the concrete Bruhat space for every field in
the UnitarySplitting statement, with no extra chart or stability hypothesis. -/

open scoped BigOperators

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable {d : ℕ}

def dotCharacter (ψ : AddChar F ℂ) (p : Local.FunctionsMetaplectic.Construction.Position F d) : AddChar (Local.FunctionsMetaplectic.Construction.Position F d) ℂ where
  toFun x := ψ (Local.FunctionsMetaplectic.Construction.dot p x)
  map_zero_eq_one' := by simp [Local.FunctionsMetaplectic.Construction.dot]
  map_add_eq_mul' x y := by simp [Local.FunctionsMetaplectic.Construction.dot, mul_add, Finset.sum_add_distrib, ψ.map_add_eq_mul]

theorem modulation_mem (_hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x)) (hunit : ∀ t, ‖ψ t‖ = 1)
    (p : Local.FunctionsMetaplectic.Construction.Position F d) {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    (fun x => ψ (Local.FunctionsMetaplectic.Construction.dot p x) * f x) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  by_cases h : ∀ n : ℕ, ‖(n : F)‖ ≤ 1
  · let : IsUltrametricDist F :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one h
    obtain ⟨hf, hc⟩ := UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp hf
    apply Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
    · exact ((LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hψ).comp_continuous
        (by unfold Local.FunctionsMetaplectic.Construction.dot; fun_prop)).mul hf
    · exact hc.mul_left
  · obtain ⟨r, ⟨e⟩⟩ := LocalTest.Construction.exists_real_coordinates_of_unbounded F h d
    apply RealChartTestSpace.Construction.realChart_character_mul_mem e (dotCharacter ψ p) ?_ (fun x => hunit _) hf
    apply hψ.comp
    unfold Local.FunctionsMetaplectic.Construction.dot
    fun_prop

theorem heisenbergFunction_mem (hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x)) (hunit : ∀ t, ‖ψ t‖ = 1)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  let q : Local.FunctionsMetaplectic.Construction.Position F d := fun i => v (Sum.inl i)
  let p : Local.FunctionsMetaplectic.Construction.Position F d := fun i => v (Sum.inr i)
  let a : F := - ∑ i, p i * (q i / 2)
  have hh := (Local.FunctionsMetaplectic.Construction.schwartzBruhat F d).smul_mem (ψ a)
    (modulation_mem hF ψ hψ hunit p (RealChartTestSpace.Construction.schwartzBruhat_translate_mem q hf))
  convert hh using 1
  funext x
  have hphase : (∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)) = a + Local.FunctionsMetaplectic.Construction.dot p x := by
    dsimp [a, p, q, Local.FunctionsMetaplectic.Construction.dot]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  change ψ _ * f (fun i => x i - v (Sum.inl i)) = ψ a * (ψ (Local.FunctionsMetaplectic.Construction.dot p x) * f (x - q))
  rw [hphase, ψ.map_add_eq_mul, mul_assoc]
  rfl

def heisenbergOperator (hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x)) (hunit : ∀ t, ‖ψ t‖ = 1)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d where
  toFun f := ⟨Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val, heisenbergFunction_mem hF ψ hψ hunit v f.property⟩
  invFun f := ⟨Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v) f.val,
    heisenbergFunction_mem hF ψ hψ hunit (-v) f.property⟩
  left_inv f := Subtype.ext (Heisenberg.Construction.heisenbergFunction_neg_left_cancel ψ v f.val)
  right_inv f := Subtype.ext (Heisenberg.Construction.heisenbergFunction_neg_right_cancel ψ v f.val)
  map_add' f g := Subtype.ext ((Heisenberg.Construction.heisenbergLinearEquiv ψ v).map_add f.val g.val)
  map_smul' z f := Subtype.ext (Oscillator.Construction.heisenbergFunction_smul d ψ v z f.val)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.HeisenbergStability.Construction

import OAI.NumberTheory.Adeles.LocalCompletions

/-! # Local Density -/

namespace OAI.NumberTheory.Adeles.LocalDensity.CompletionFactors

noncomputable section

/-! Density of global algebraic integers in the integer ring of a finite completion. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology WithZero

variable {F : Type*} [Field F] [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))

theorem local_integer_of_field_mem_closure {x : F} (hx : v.valuation F x ≤ 1) :
    algebraMap F (v.adicCompletion F) x ∈
      closure (Set.range (algebraMap (𝓞 F) (v.adicCompletion F))) := by
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp (hU.mem_nhds hxU)
  let δ : (ℤᵐ⁰)ˣ := Units.map
    (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := .ofClass (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).toMonoidHom γ
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hx δ
  refine ⟨algebraMap (𝓞 F) (v.adicCompletion F) a, hγ ?_, ⟨a, rfl⟩⟩
  change Valued.v.restrict (algebraMap (𝓞 F) (v.adicCompletion F) a -
    algebraMap F (v.adicCompletion F) x) < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  have hs : algebraMap (𝓞 F) (v.adicCompletion F) a -
      algebraMap F (v.adicCompletion F) x =
        algebraMap F (v.adicCompletion F) ((a : F) - x) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  rw [hs]
  change Valued.v (((a : F) - x : F) : v.adicCompletion F) < _
  rw [adicCompletion.valued_coe]
  exact ha

/-- Every local integer is approximated by global algebraic integers. -/
theorem local_integer_mem_closure (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) :
    x ∈ closure (Set.range (algebraMap (𝓞 F) (v.adicCompletion F))) := by
  have hp : x ∉ v.adicCompletionIntegers F ∨
      x ∈ closure (Set.range (algebraMap (𝓞 F) (v.adicCompletion F))) := by
    refine (v.denseRange_algebraMap F).induction_on
      (p := fun y => y ∉ v.adicCompletionIntegers F ∨
        y ∈ closure (Set.range (algebraMap (𝓞 F) (v.adicCompletion F)))) x ?_ ?_
    · exact (Valued.isOpen_valuationSubring (v.adicCompletion F)).isClosed_compl.union
        isClosed_closure
    · intro a
      by_cases ha : v.valuation F a ≤ 1
      · exact Or.inr (local_integer_of_field_mem_closure v ha)
      · exact Or.inl (by
          change ¬ Valued.v (a : v.adicCompletion F) ≤ 1
          rwa [adicCompletion.valued_coe])
  exact hp.resolve_left (not_not_intro hx)

end

end OAI.NumberTheory.Adeles.LocalDensity.CompletionFactors

import OAI.NumberTheory.Adeles.LocalNorms
import OAI.NumberTheory.Adeles.LocalDensity

/-! # Local Integers -/

namespace OAI.NumberTheory.Adeles.LocalIntegers.CompletionFactors

noncomputable section

/-! Integral elements and their images under the canonical local norms. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver WithZero

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- A global algebraic integer has locally integral norm. -/
theorem finiteLocalNorm_global_integer (x : 𝓞 E) :
    LocalNorms.CompletionFactors.finiteLocalNorm v w (algebraMap E (w.adicCompletion E) (x : E)) ∈
      v.adicCompletionIntegers F := by
  have hx : IsIntegral ℤ (algebraMap E (w.adicCompletion E) (x : E)) :=
    x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ E (w.adicCompletion E))
  have hn := Algebra.isIntegral_norm (v.adicCompletion F) hx
  exact (Valuation.valuationSubring.integers
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).isIntegral_iff_v_le_one.mp
      (hn.tower_top (A := v.adicCompletionIntegers F))

/-- The local field norm preserves the valuation rings. -/
theorem finiteLocalNorm_integer (x : w.adicCompletion E)
    (hx : x ∈ w.adicCompletionIntegers E) :
    LocalNorms.CompletionFactors.finiteLocalNorm v w x ∈ v.adicCompletionIntegers F := by
  have hc : IsClosed {y : w.adicCompletion E |
      LocalNorms.CompletionFactors.finiteLocalNorm v w y ∈ v.adicCompletionIntegers F} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion F)).preimage
      (LocalNorms.CompletionFactors.continuous_finiteLocalNorm v w)
  have hs : Set.range (algebraMap (𝓞 E) (w.adicCompletion E)) ⊆
      {y | LocalNorms.CompletionFactors.finiteLocalNorm v w y ∈ v.adicCompletionIntegers F} := by
    rintro y ⟨a, rfl⟩
    change LocalNorms.CompletionFactors.finiteLocalNorm v w (algebraMap (𝓞 E) (w.adicCompletion E) a) ∈
      v.adicCompletionIntegers F
    rw [IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E)]
    exact finiteLocalNorm_global_integer v w a
  exact closure_minimal hs hc (LocalDensity.CompletionFactors.local_integer_mem_closure w x hx)

/-- Integral local units are sent to integral local units. -/
theorem finiteLocalIdeleNorm_integral_unit (a : (w.adicCompletion E)ˣ)
    (ha : a ∈ (Submonoid.ofClass (w.adicCompletionIntegers E)).units) :
    LocalNorms.CompletionFactors.finiteLocalIdeleNorm v w a ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units :=
  ⟨finiteLocalNorm_integer v w a.val ha.1, finiteLocalNorm_integer v w a.inv ha.2⟩

end

end OAI.NumberTheory.Adeles.LocalIntegers.CompletionFactors

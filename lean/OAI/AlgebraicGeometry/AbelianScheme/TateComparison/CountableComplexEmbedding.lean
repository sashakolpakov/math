import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Cardinality
import Lean.Util.CollectAxioms

/-! # Countable Complex Embedding -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableComplexEmbedding

noncomputable section

/-! A countable characteristic-zero field embeds in the complex numbers.
This applies to fields of definition of geometric moduli points; the
arbitrary algebraically closed residue extension need not embed in ℂ. -/

open scoped Cardinal

theorem countable_field_has_complex_embedding (F : Type) [Field F]
    [CharZero F] [Countable F] : Nonempty (F →+* ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ F
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have hcard : Cardinal.mk ℂ = Cardinal.mk t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      _ ht Cardinal.mk_le_aleph0 Cardinal.aleph0_lt_mk
  have hst : Cardinal.mk s ≤ Cardinal.mk t := by
    rw [← hcard]
    exact Cardinal.mk_le_aleph0.trans Cardinal.aleph0_lt_mk.le
  obtain ⟨e⟩ := (Cardinal.le_def s t).mp hst
  let w : s → ℂ := Subtype.val ∘ e
  have hw : AlgebraicIndependent ℚ w := ht.1.comp e e.injective
  let B := Algebra.adjoin ℚ (Set.range (Subtype.val : s → F))
  let f : B →ₐ[ℚ] ℂ := (Algebra.adjoin ℚ (Set.range w)).val.comp
    (hs.1.aevalEquiv.symm.trans hw.aevalEquiv).toAlgHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (hs.1.aevalEquiv.symm.trans hw.aevalEquiv).injective
  let : Algebra B ℂ := f.toRingHom.toAlgebra
  have : Module.IsTorsionFree B ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hf
  have : Algebra.IsAlgebraic B F := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : F →ₐ[B] ℂ).toRingHom⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableComplexEmbedding

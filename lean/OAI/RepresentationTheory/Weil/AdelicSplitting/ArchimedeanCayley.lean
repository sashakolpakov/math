import OAI.RepresentationTheory.Weil.AdelicSplitting.DenseHilbert
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeakLinearity
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeakCayleyBound

/-! # Archimedean Cayley -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayley.Construction

noncomputable section

/-! Construction of the bounded Hilbert-space operator representing the
corrected weak Cayley integral. Its existence is derived from the checked
integral bound and sesquilinearity. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure]
variable (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
variable (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
variable (hbound : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  ‖CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val‖ ≤
    ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ * ‖UnitarySplitting.Weak.Construction.testToL2 k N h‖)

include hk hc hu W hW hbound in
theorem correctedWeakOpenCell_representable (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ∃ v : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N),
      ‖v‖ ≤ ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ ∧
      ∀ h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N, ⟪UnitarySplitting.Weak.Construction.testToL2 k N h, v⟫_ℂ =
        CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val := by
  apply DenseHilbert.Construction.exists_vector_of_bounded_conjugate_linear
    (UnitarySplitting.Weak.Construction.testToL2 k N) (ArchimedeanSpace.Construction.archimedean_testToL2_dense N)
    (fun h => CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val)
    (ArchimedeanWeakLinearity.Construction.correctedWeakOpenCell_add_right hk ψ hc hu ν g hg W hW f)
    (fun z h => ArchimedeanWeakLinearity.Construction.correctedWeakOpenCell_smul_right hk ψ hc hu ν g hg z f h)
    _ (norm_nonneg _) (hbound f)

def correctedCayleyHilbertVector (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) :=
  Classical.choose (correctedWeakOpenCell_representable hk ψ hc hu ν g hg W hW hbound f)

theorem correctedCayleyHilbertVector_norm (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ‖correctedCayleyHilbertVector hk ψ hc hu ν g hg W hW hbound f‖ ≤
      ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ :=
  (Classical.choose_spec (correctedWeakOpenCell_representable hk ψ hc hu ν g hg W hW hbound f)).1

theorem correctedCayleyHilbertVector_pairing (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ⟪UnitarySplitting.Weak.Construction.testToL2 k N h,
      correctedCayleyHilbertVector hk ψ hc hu ν g hg W hW hbound f⟫_ℂ =
        CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val :=
  (Classical.choose_spec (correctedWeakOpenCell_representable hk ψ hc hu ν g hg W hW hbound f)).2 h

def correctedCayleyHilbertTestOperator :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat k N →ₗ[ℂ] Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) where
  toFun := correctedCayleyHilbertVector hk ψ hc hu ν g hg W hW hbound
  map_add' f₁ f₂ := by
    apply DenseHilbert.Construction.eq_of_dense_test_pairings (UnitarySplitting.Weak.Construction.testToL2 k N) (ArchimedeanSpace.Construction.archimedean_testToL2_dense N)
    intro h
    rw [correctedCayleyHilbertVector_pairing, inner_add_right,
      correctedCayleyHilbertVector_pairing, correctedCayleyHilbertVector_pairing]
    exact ArchimedeanWeakLinearity.Construction.correctedWeakOpenCell_add_left hk ψ hc hu ν g hg W hW f₁ f₂ h
  map_smul' z f := by
    apply DenseHilbert.Construction.eq_of_dense_test_pairings (UnitarySplitting.Weak.Construction.testToL2 k N) (ArchimedeanSpace.Construction.archimedean_testToL2_dense N)
    intro h
    rw [correctedCayleyHilbertVector_pairing, inner_smul_right, correctedCayleyHilbertVector_pairing]
    exact ArchimedeanWeakLinearity.Construction.correctedWeakOpenCell_smul_left hk ψ hc hu ν g hg z f h

def correctedCayleyHilbertOperator :
    Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) →L[ℂ] Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) :=
  (correctedCayleyHilbertTestOperator hk ψ hc hu ν g hg W hW hbound).extendOfNorm
    (UnitarySplitting.Weak.Construction.testToL2 k N)

theorem correctedCayleyHilbertOperator_test (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    correctedCayleyHilbertOperator hk ψ hc hu ν g hg W hW hbound
        (UnitarySplitting.Weak.Construction.testToL2 k N f) =
      correctedCayleyHilbertVector hk ψ hc hu ν g hg W hW hbound f := by
  apply LinearMap.extendOfNorm_eq (ArchimedeanSpace.Construction.archimedean_testToL2_dense N)
  refine ⟨1, fun h => ?_⟩
  simpa only [one_mul] using! correctedCayleyHilbertVector_norm hk ψ hc hu ν g hg W hW hbound h

theorem correctedCayleyHilbertOperator_contracts (x : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)) :
    ‖correctedCayleyHilbertOperator hk ψ hc hu ν g hg W hW hbound x‖ ≤ ‖x‖ := by
  have hb (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      ‖correctedCayleyHilbertTestOperator hk ψ hc hu ν g hg W hW hbound f‖ ≤
        1 * ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ := by
    simpa only [one_mul] using! correctedCayleyHilbertVector_norm hk ψ hc hu ν g hg W hW hbound f
  simpa only [one_mul] using!
    LinearMap.norm_extendOfNorm_apply_le (ArchimedeanSpace.Construction.archimedean_testToL2_dense N) 1 hb x

theorem correctedCayleyHilbertOperator_pairing (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ⟪UnitarySplitting.Weak.Construction.testToL2 k N h,
      correctedCayleyHilbertOperator hk ψ hc hu ν g hg W hW hbound
        (UnitarySplitting.Weak.Construction.testToL2 k N f)⟫_ℂ =
      CorrectedNormalization.Construction.correctedWeakOpenCell k N ψ ν g hg f.val h.val := by
  rw [correctedCayleyHilbertOperator_test, correctedCayleyHilbertVector_pairing]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayley.Construction

import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Compact Standard Unitary -/

namespace OAI.RepresentationTheory.Theta.Adelic.CompactStandardUnitary

noncomputable section

/-! Compactness of the standard positive-definite special-unitary group
in its actual matrix-unit topology. -/

open scoped Classical _root_.Matrix.Norms.Elementwise

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem unitary_entry_norm_le_one (M : Matrix I I ℂ) (hM : M.conjTranspose * M = 1) (i j : I) :
    ‖M i j‖ ≤ 1 := by
  have he := congrArg (fun A : Matrix I I ℂ => (A j j).re) hM
  have hs : ∑ k, Complex.normSq (M k j) = 1 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.normSq_apply, Complex.mul_re] using he
  have hi := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (M k j))
    (Finset.mem_univ i)
  rw [hs, Complex.normSq_eq_norm_sq] at hi
  nlinarith [norm_nonneg (M i j)]

def standardUnitaryMatrices : Set (Matrix I I ℂ) :=
  {M | M.conjTranspose * M = 1 ∧ M.det = 1}

theorem standardUnitaryMatrices_compact : IsCompact (standardUnitaryMatrices (I := I)) := by
  let : ProperSpace (Matrix I I ℂ) := inferInstanceAs (ProperSpace (I → I → ℂ))
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const)
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1, ?_⟩
    intro M hM
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    exact unitary_entry_norm_le_one M hM.1 i j

def standardUnitaryOfMatrix (M : standardUnitaryMatrices (I := I)) : SpecialUnitary.SU (1 : Matrix I I ℂ) :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨M.val, M.property.2⟩,
    by
      change M.val.conjTranspose * 1 * M.val = 1
      simpa only [mul_one] using M.property.1,
    Matrix.SpecialLinearGroup.coeToGL_det ⟨M.val, M.property.2⟩⟩

theorem standardUnitaryOfMatrix_inverse (M : standardUnitaryMatrices (I := I)) :
    ((standardUnitaryOfMatrix M).val⁻¹).val = M.val.conjTranspose := by
  exact (left_inv_eq_right_inv M.property.1 (standardUnitaryOfMatrix M).val.val_inv).symm

theorem standardUnitaryOfMatrix_continuous : Continuous (standardUnitaryOfMatrix (I := I)) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · exact (show Continuous (fun M : standardUnitaryMatrices (I := I) => M.val.conjTranspose)
      by fun_prop).congr (fun M => (standardUnitaryOfMatrix_inverse M).symm)

theorem standardUnitary_compact : CompactSpace (SpecialUnitary.SU (1 : Matrix I I ℂ)) := by
  have hs : Function.Surjective (standardUnitaryOfMatrix (I := I)) := by
    intro g
    refine ⟨⟨g.val.val, ?_, congrArg Units.val g.property.2⟩, ?_⟩
    · have h : g.val.val.conjTranspose * 1 * g.val.val = 1 := g.property.1
      simpa only [mul_one] using h
    · apply Subtype.ext
      apply Units.ext
      rfl
  have hc := standardUnitaryMatrices_compact (I := I)
  let : CompactSpace (standardUnitaryMatrices (I := I)) := isCompact_iff_compactSpace.mp hc
  constructor
  have h := isCompact_univ.image (standardUnitaryOfMatrix_continuous (I := I))
  simpa only [Set.image_univ, hs.range_eq] using h

end

end OAI.RepresentationTheory.Theta.Adelic.CompactStandardUnitary

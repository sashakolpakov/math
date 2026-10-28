import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingSymmetricWeights
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvolutionSpectralDecomposition

/-! # Eigenbasis Span -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.EigenbasisSpan.Construction

noncomputable section

/-! Positive eigenspaces are spanned by the positive-weight members
of an orthonormal eigenbasis. -/

open scoped Classical
open _root_.Module.End

theorem positiveSpectralSubmodule_eq_eigenbasis_span
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [Fintype ι]
    (b : OrthonormalBasis ι ℝ L) (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : ι → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule H.toLinearMap ⊤ =
      Submodule.span ℝ (Set.range (fun i : {i : ι // 0 < w i} => b i.val)) := by
  have hset : Set.range (fun i : {i : ι // 0 < w i} => b i.val) = b.toBasis '' {i | 0 < w i} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr x hx
    rw [hset, b.toBasis.mem_span_image]
    intro i hi
    have hn : b.repr x i ≠ 0 := by
      have hi' : b.toBasis.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
      simpa only [OrthonormalBasis.coe_toBasis_repr_apply] using hi'
    have he := congrArg (fun y => b.repr y i) (mem_eigenspace_iff.mp hx.2)
    change b.repr (H x) i = b.repr (r • x) i at he
    rw [CommutingSymmetricWeights.Construction.orthonormal_eigen_coordinate b H hH w heig] at he
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at he
    change 0 < w i
    rwa [mul_right_cancel₀ hn he]
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact InvolutionSpectralDecomposition.Construction.mem_positiveSpectralSubmodule H.toLinearMap ⊤ i.property (Submodule.mem_top) (heig i.val)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.EigenbasisSpan.Construction

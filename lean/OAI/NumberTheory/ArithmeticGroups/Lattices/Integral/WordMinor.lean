import OAI.NumberTheory.ArithmeticGroups.Lattices.WordMinorNaturality
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Lie

/-! # Word Minor -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.WordMinor.Construction

noncomputable section

/-! Word minors of integral Lie matrices and integral vectors have
values in the discrete integer Minkowski lattice. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem integral_lie_word_minor_mem
    {k ι : Type} [Field k] [NumberField k] {n d : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (A : ι → Lie.Construction.integralLieOrder G)
    (q : Finite.WordMinors.Construction.boundedWordMinorIndex ι n d) (x : Fin n → 𝓞 k) :
    mixedEmbedding k (Finite.WordMinors.Construction.boundedWordMinor q (fun i => (A i).val.val) (fun i => (x i : k))) ∈
      mixedEmbedding.integerLattice k := by
  have hA (i : ι) : ∃ B : Matrix (Fin n) (Fin n) (𝓞 k),
      B.map (algebraMap (𝓞 k) k) = (A i).val.val :=
    (Lie.Construction.mem_integralLieLattice G (A i).val).mp (A i).property
  choose B hB using hA
  refine ⟨Finite.WordMinors.Construction.boundedWordMinor q B x, ?_⟩
  change mixedEmbedding k ((algebraMap (𝓞 k) k) (Finite.WordMinors.Construction.boundedWordMinor q B x)) = _
  rw [WordMinorNaturality.Construction.boundedWordMinor_map]
  simp only [hB]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.WordMinor.Construction

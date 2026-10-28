import OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentSpan
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockDecomposition

/-! # Local Product Tangent -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalProductTangent

noncomputable section

/-! The full local-product tangent span is the product of the actual
local tangent spans whenever the factors share a scalar field. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem finiteMatrixProductHom_range (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) :
    range (PrimeBlockDecomposition.finiteMatrixProductHom G v) =
      Set.pi univ (fun i => range (MatrixOpenness.localMatrixMonoidHom G (v i))) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩ i _
    exact ⟨g i, rfl⟩
  · intro hx
    choose g hg using fun i => hx i (mem_univ i)
    exact ⟨g, funext hg⟩

theorem localProductTangentSpan_eq_pi {κ : Type} [Field κ]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F))
    [∀ i, Algebra κ ((v i).adicCompletion F)]
    [∀ i, ContinuousConstSMul κ ((v i).adicCompletion F)] :
    Submodule.span κ (tangentConeAt κ (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1) =
      Submodule.pi univ (fun i => TangentBracket.matrixTangentSpanOver (K := (v i).adicCompletion F)
        (κ := κ) G (LocalAdeles.localEmbedding (Sum.inr (v i))) ⊤) := by
  rw [finiteMatrixProductHom_range]
  have h := ProductTangentSpan.tangentSpan_pi (κ := κ) (fun i => range (MatrixOpenness.localMatrixMonoidHom G (v i))) 1
    (fun i => subset_closure ⟨1, map_one _⟩)
  convert! h using 1
  congr 1
  funext i
  simp only [TangentBracket.matrixTangentSpanOver, TangentBracket.matrixTangentConeOver, Subgroup.coe_top, image_univ]
  rfl

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalProductTangent

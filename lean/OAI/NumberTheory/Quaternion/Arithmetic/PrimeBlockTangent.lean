import OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentLie
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockInfinitesimal

/-! # Prime Block Tangent -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockTangent

noncomputable section

/-! Full tangent space in a residue-prime block follows from rational
commensuration, full commensurator tangent, and nonzero factor projections.
Simplicity is deduced from the algebraic group hypotheses. -/

open scoped Classical _root_.NumberField OAI.NumberTheory.Quaternion.Arithmetic.ProductLieIdeals.LieProducts
open IsDedekindDomain Set

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem primeBlock_tangentSpan_eq_of_nonzero_projections
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i))
    (H R : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hcomm : ∀ g ∈ R, (H.map (MulAut.conj g).toMonoidHom).Commensurable H) :
    letI : ∀ i, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v i).adicCompletion F) :=
      fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
    let W := fun J : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) =>
      Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
          (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (J.topologicalClosure : Set _)) 1)
    let T := Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1)
    W R = T → (∀ i, ∃ a ∈ W H, a i ≠ 0) → W H = T := by
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : NontriviallyNormedField κ := TangentBracket.finiteClosedPrimeNontriviallyNormedField v₀
  let : ∀ i, Algebra κ ((v i).adicCompletion F) := fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  let : ∀ i, FiniteDimensional κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_finiteDimensional v₀ (v i) (hv i)
  let : ∀ i, ContinuousSMul κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_continuousSMul v₀ (v i) (hv i)
  intro W T hR hproj
  let B := fun i => SimpleLie.lieSubalgebraRestrictScalars (κ := κ)
    (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange (K := (v i).adicCompletion F)
      G (LocalAdeles.localEmbedding (Sum.inr (v i)))))
  let : ∀ i, LieAlgebra.IsSimple κ (B i) :=
    fun i => PrimeBlockInfinitesimal.primeBlock_infinitesimal_isSimple G hsimple hsemi v₀ (v i) (hv i)
  exact ProductTangentLie.product_tangentSpan_eq_of_simple_factors (κ := κ) G v B H R hcomm
    (W H).closed_of_finiteDimensional
    (PrimeBlockInfinitesimal.primeBlock_tangentSpan_eq_infinitesimal_product G hconn v₀ v hv) hR hproj

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockTangent

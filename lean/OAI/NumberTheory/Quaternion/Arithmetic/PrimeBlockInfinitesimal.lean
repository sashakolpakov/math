import OAI.NumberTheory.Quaternion.Arithmetic.LocalProductTangent
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockLocalTangent
import OAI.NumberTheory.Quaternion.Arithmetic.SimpleLie
import OAI.NumberTheory.Quaternion.Arithmetic.LocalAlgebraicLieSimplicity

/-! # Prime Block Infinitesimal -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockInfinitesimal

noncomputable section

/-! A residue-prime block has the product infinitesimal tangent space,
and each of its factors is simple over the common prime scalar field. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem primeBlock_tangentSpan_eq_infinitesimal_product {ι : Type*} [Fintype ι]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected)
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, LocalCompletion.residuePrime v₀ = LocalCompletion.residuePrime (v i)) :
    letI : ∀ i, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v i).adicCompletion F) :=
      fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
    Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
          (range (PrimeBlockDecomposition.finiteMatrixProductHom G v)) 1) =
      Submodule.pi univ (fun i =>
        (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange (K := (v i).adicCompletion F)
          G (LocalAdeles.localEmbedding (Sum.inr (v i))))).toSubmodule.restrictScalars
            (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))) := by
  let κ := TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)
  let : ∀ i, Algebra κ ((v i).adicCompletion F) := fun i => PrimeField.primeBlockScalarAlgebra v₀ (v i) (hv i)
  let : ∀ i, ContinuousSMul κ ((v i).adicCompletion F) :=
    fun i => PrimeField.primeBlockScalar_continuousSMul v₀ (v i) (hv i)
  rw [LocalProductTangent.localProductTangentSpan_eq_pi]
  congr 1
  funext i
  exact PrimeBlockLocalTangent.primeBlock_local_tangentSpan_eq_infinitesimal G hG v₀ (v i) (hv i)

theorem primeBlock_infinitesimal_isSimple (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (v w : HeightOneSpectrum (𝓞 F)) (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    letI := PrimeField.primeBlockScalarAlgebra v w hvw
    LieAlgebra.IsSimple (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      (SimpleLie.lieSubalgebraRestrictScalars (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F))
        (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange (K := w.adicCompletion F)
          G (LocalAdeles.localEmbedding (Sum.inr w))))) := by
  let : Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (w.adicCompletion F) :=
    PrimeField.primeBlockScalarAlgebra v w hvw
  let L := ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange (K := w.adicCompletion F)
    G (LocalAdeles.localEmbedding (Sum.inr w)))
  let : LieAlgebra.IsSimple (w.adicCompletion F) L :=
    LocalAlgebraicLieSimplicity.infinitesimal_simple_over_extension (K := w.adicCompletion F) G hsimple hsemi
  exact SimpleLie.lieSubalgebraRestrictScalars_isSimple L

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockInfinitesimal

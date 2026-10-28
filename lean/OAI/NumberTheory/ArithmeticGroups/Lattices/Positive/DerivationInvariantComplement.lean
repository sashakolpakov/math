import OAI.NumberTheory.ArithmeticGroups.Lattices.TransportedInvariantComplement
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FlowHilbertSymmetry
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ConjugationBracketOperators

/-! # Derivation Invariant Complement -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationInvariantComplement.Construction

noncomputable section

/-! Positive bracket derivations have a complementary subspace of
the ambient positive operators preserved by regular split conjugation. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

local instance positiveComplementEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance positiveComplementEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance positiveComplementEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

def positiveDerivationsInWeightRaising {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : OrthonormalBasis (Fin m) ℝ L) (H : L →L[ℝ] L) (w : Fin m → ℝ) :
    Submodule ℝ (DerivationNilpotence.Construction.weightRaisingOperators b w) :=
  (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H).comap (DerivationNilpotence.Construction.weightRaisingOperators b w).subtype

theorem positiveDerivationsInWeightRaising_split_invariant
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (t : ℝ) (X : DerivationNilpotence.Construction.weightRaisingOperators b w)
    (hX : X ∈ positiveDerivationsInWeightRaising B b H w) :
    Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH.1 w heig t X ∈ positiveDerivationsInWeightRaising B b H w := by
  change (Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH.1 w heig t X).val ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H
  rw [Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow_val]
  exact Split.ConjugationBracketOperators.Construction.split_conjugation_preserves_positive_derivations B b H hH w heig t X.val hX

theorem positive_derivations_exists_split_invariant_complement
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    ∃ U : Submodule ℝ (DerivationNilpotence.Construction.weightRaisingOperators b w),
      IsCompl U (positiveDerivationsInWeightRaising B b H w) ∧
      ∀ t X, X ∈ U → Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH.1 w heig t X ∈ U := by
  let W := DerivationNilpotence.Construction.weightRaisingOperators b w
  let Φ := (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis).submoduleMap W
  apply TransportedInvariantComplement.Construction.exists_invariant_complement_of_transported_symmetry Φ
    (positiveDerivationsInWeightRaising B b H w)
    (fun t => (Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH.1 w heig t).toContinuousLinearMap)
  · intro t X Y
    change inner ℝ
      (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis (Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH.1 w heig t X).val)
      (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis Y.val) =
      inner ℝ (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis X.val)
        (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis (Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH.1 w heig t Y).val)
    rw [Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow_val, Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow_val]
    exact Split.FlowHilbertSymmetry.Construction.split_conjugation_euclidean_inner b H hH.1 w heig t X.val Y.val
  · exact positiveDerivationsInWeightRaising_split_invariant B b H hH w heig

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationInvariantComplement.Construction

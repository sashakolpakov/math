import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantSubmoduleEquivalence
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ConjugationContraction

/-! # Raising Split Flow -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingSplitFlow.Construction

noncomputable section

/-! The regular split conjugation flow is a continuous linear
equivalence of the ambient weight-raising space and contracts it. -/

open NormedSpace Filter
open scoped _root_.Topology

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

local instance weightSplitFlowEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance weightSplitFlowEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance weightSplitFlowEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance weightSplitFlow_complete : CompleteSpace L := FiniteDimensional.complete ℝ L

def weightRaisingSplitFlow {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) (t : ℝ) :
    Positive.DerivationNilpotence.Construction.weightRaisingOperators b w ≃L[ℝ] Positive.DerivationNilpotence.Construction.weightRaisingOperators b w :=
  InvariantSubmoduleEquivalence.Construction.invariantSubmoduleEquiv
    (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv ((-t) • H)).conjContinuousAlgEquiv.toContinuousLinearEquiv
    (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)
    (fun X hX => by
      change exp ((-t) • H) * X * exp (-((-t) • H)) ∈ _
      simpa only [neg_smul, neg_neg] using
        ConjugationContraction.Construction.split_conjugation_preserves_weightRaising b H hH w heig t X hX)
    (fun X hX => by
      change exp (-((-t) • H)) * X * exp ((-t) • H) ∈ _
      simpa only [neg_smul, neg_neg] using
        ConjugationContraction.Construction.split_conjugation_preserves_weightRaising b H hH w heig (-t) X hX)

theorem weightRaisingSplitFlow_val {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) (t : ℝ)
    (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    (weightRaisingSplitFlow b H hH w heig t X).val =
      exp ((-t) • H) * X.val * exp (t • H) := by
  change exp ((-t) • H) * X.val * exp (-((-t) • H)) = _
  simp only [neg_smul, neg_neg]

theorem weightRaisingSplitFlow_contracts {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    Tendsto (fun t : ℝ => weightRaisingSplitFlow b H hH w heig t X) atTop (𝓝 0) := by
  apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
  change Tendsto (fun t : ℝ => (weightRaisingSplitFlow b H hH w heig t X).val) atTop (𝓝 0)
  simp_rw [weightRaisingSplitFlow_val]
  exact ConjugationContraction.Construction.split_conjugation_contracts_weightRaising b H hH w heig X.val X.property

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingSplitFlow.Construction

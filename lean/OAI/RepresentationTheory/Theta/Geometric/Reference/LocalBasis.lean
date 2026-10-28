import OAI.RepresentationTheory.Theta.Geometric.Local.IntegralDetection

/-! # Local Basis -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The same fixed integral reference basis gives rational and completed
bases. Their vectors retain the literal original split embeddings. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hdegree : Module.finrank ℚ E = 2 * s)

include hg in
theorem Data.ActiveHeckeThetaData.referenceLattice_rationalSpan :
    Submodule.span ℚ (D.pel.reference.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤ := by
  rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
  exact h.2.1

include hdegree in
omit [NumberField.IsCMField E] in
theorem Data.ActiveHeckeThetaData.referenceLattice_rank : Fintype.card (Fin (2 * (3 * s))) = Module.finrank ℚ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := by
  change Fintype.card (Fin (2 * (3 * s))) = Module.finrank ℚ (Fin 3 → E)
  rw [Module.finrank_pi_fintype]
  simp only [Fintype.card_fin, hdegree, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

def Data.ActiveHeckeThetaData.referenceQBasis : Module.Basis (Fin (2 * (3 * s))) ℚ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :=
  IntegralRationalBasis.integralRationalBasis D.pel.reference.lattice (D.pel.reference.referenceBasis hg.reference_admissible)
    (D.referenceLattice_rationalSpan hg) (Data.ActiveHeckeThetaData.referenceLattice_rank hdegree)

theorem Data.ActiveHeckeThetaData.referenceQBasis_apply (i : Fin (2 * (3 * s))) :
    D.referenceQBasis hg hdegree i = (D.pel.reference.referenceBasis hg.reference_admissible i).val :=
  IntegralRationalBasis.integralRationalBasis_apply _ _ _ _ i

theorem Data.ActiveHeckeThetaData.referenceQBasis_span :
    Submodule.span ℤ (Set.range (D.referenceQBasis hg hdegree)) = D.pel.reference.lattice :=
  IntegralRationalBasis.integralRationalBasis_span _ _ _ _

def Data.ActiveHeckeThetaData.jointQBasis (hgood : D.pel.IsGoodCompletelySplitPrime) :
    Module.Basis (Fin (2 * (3 * s))) ℚ_[q] (Fin s × Bool → Fin 3 → ℚ_[q]) :=
  ((D.referenceQBasis hg hdegree).baseChange ℚ_[q]).map (D.jointRationalCompletion hgood hdegree)

theorem Data.ActiveHeckeThetaData.jointQBasis_apply (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (i : Fin (2 * (3 * s))) : D.jointQBasis hg hdegree hgood i =
      D.jointLocalEmbedding (D.pel.reference.referenceBasis hg.reference_admissible i).val := by
  change D.jointRationalCompletion hgood hdegree ((D.referenceQBasis hg hdegree).baseChange ℚ_[q] i) = _
  rw [Module.Basis.baseChange_apply, D.referenceQBasis_apply, D.jointRationalCompletion_one_tmul hgood hdegree hc]

theorem Data.ActiveHeckeThetaData.jointQBasis_mem (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (i : Fin (2 * (3 * s))) : D.jointQBasis hg hdegree hgood i ∈ D.jointLocalLattice := by
  rw [D.jointQBasis_apply hg hdegree hc hgood]
  exact Submodule.subset_span ⟨_, (D.pel.reference.referenceBasis hg.reference_admissible i).property, rfl⟩

end

end OAI.RepresentationTheory.Theta.Geometric

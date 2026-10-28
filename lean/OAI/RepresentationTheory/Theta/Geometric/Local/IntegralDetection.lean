import OAI.RepresentationTheory.Theta.Geometric.SplitLocalLattice
import OAI.RepresentationTheory.Theta.Geometric.JointRationalCompletion
import OAI.RepresentationTheory.Theta.Geometric.IntegralRationalBasis
import OAI.RepresentationTheory.Theta.Geometric.LatticeSaturation
import OAI.RepresentationTheory.Theta.Geometric.AwayLattice
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis

/-! # Integral Detection -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Literal integral membership in the reference lattice is detected by
all its original split coordinates together with away-q membership. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.referenceLattice_of_jointLocal_and_away (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hlocal : D.jointLocalEmbedding v ∈ D.jointLocalLattice) (haway : v ∈ D.awayLattice) :
    v ∈ D.pel.reference.lattice := by
  have hspan : Submodule.span ℚ (D.pel.reference.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤ := by
    rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
    exact h.2.1
  have hrank : Fintype.card (Fin (2 * (3 * s))) = Module.finrank ℚ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := by
    change Fintype.card (Fin (2 * (3 * s))) = Module.finrank ℚ (Fin 3 → E)
    rw [Module.finrank_pi_fintype]
    simp only [Fintype.card_fin, hdegree, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  let b := IntegralRationalBasis.integralRationalBasis D.pel.reference.lattice
    (D.pel.reference.referenceBasis hg.reference_admissible) hspan hrank
  let e := D.jointRationalCompletion hgood hdegree
  apply LatticeSaturation.completedLattice_power_saturation q b D.pel.reference.lattice
    (IntegralRationalBasis.integralRationalBasis_span _ _ _ _) e v
  · change e (1 ⊗ₜ[ℚ] v) ∈ Submodule.span ℤ_[q]
      ((fun x => e (1 ⊗ₜ[ℚ] x)) '' (D.pel.reference.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)))
    simpa only [e, D.jointRationalCompletion_one_tmul hgood hdegree hc, Data.ActiveHeckeThetaData.jointLocalLattice] using hlocal
  · exact (D.mem_awayLattice_iff v).mp haway

theorem Data.ActiveHeckeThetaData.referenceLattice_of_local_and_away (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hlocal : ∀ w, (fun i => D.localEmbedding w (v i)) ∈ Data.ActiveHeckeThetaData.standardLocalLattice (q := q))
    (haway : v ∈ D.awayLattice) : v ∈ D.pel.reference.lattice :=
  D.referenceLattice_of_jointLocal_and_away hg hc hgood hdegree v
    ((D.jointLocalLattice_standard hg hc hgood _).mpr hlocal) haway

end

end OAI.RepresentationTheory.Theta.Geometric

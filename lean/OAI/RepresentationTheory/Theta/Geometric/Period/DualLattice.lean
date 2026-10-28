import OAI.RepresentationTheory.Theta.Geometric.IntegralDualLattice
import OAI.RepresentationTheory.Theta.Geometric.Period.Hermitian
import OAI.RepresentationTheory.Theta.Geometric.Reference.Basis

/-! # Dual Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The integral dual of the actual period lattice, with its perfect
pairing and the original integral polarization retained. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.periodImaginaryForm_skew (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (u v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.periodImaginaryForm hg x v u = -D.periodImaginaryForm hg x u v := by
  simp only [Data.ActiveHeckeThetaData.periodImaginaryForm_apply, D.periodHermitian_hermitian hg x u v,
    Complex.star_def, Complex.conj_im]

theorem Data.ActiveHeckeThetaData.periodImaginaryForm_nondegenerate (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    (D.periodImaginaryForm hg x).Nondegenerate := by
  have hleft : (D.periodImaginaryForm hg x).SeparatingLeft := by
    intro u hu
    by_contra hne
    have hz := hu (Complex.I • u)
    have hpos := D.periodHermitian_positive hg x u hne
    rw [Data.ActiveHeckeThetaData.periodImaginaryForm_apply, map_smul] at hz
    simp only [smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add] at hz
    exact (ne_of_gt hpos) hz
  refine ⟨hleft, ?_⟩
  intro u hu
  apply hleft u
  intro v
  rw [D.periodImaginaryForm_skew hg x v u, hu v, neg_zero]

theorem Data.ActiveHeckeThetaData.periodImaginaryForm_integral (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (u v : D.pel.reference.lattice) :
    D.periodImaginaryForm hg x (D.periodLatticeEquiv hg x u).val
      (D.periodLatticeEquiv hg x v).val = (D.pel.reference.integralForm u v : ℝ) := by
  change D.periodImaginaryForm hg x (D.periodReferenceEmbedding x.val u.val)
    (D.periodReferenceEmbedding x.val v.val) = _
  rw [Data.ActiveHeckeThetaData.periodImaginaryForm_apply, D.periodHermitian_reference]
  rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, _, hi, _⟩
  rw [← hi u v]
  exact Rat.cast_intCast _

def Data.ActiveHeckeThetaData.periodDualLattice (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Submodule ℤ (D.canonicalPeriodData hg x).space := by
  change Submodule ℤ (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s))
  exact
  LinearMap.BilinForm.dualSubmodule (D.periodImaginaryForm hg x)
    (D.canonicalPeriodData hg x).periodIntegerLattice

instance Data.ActiveHeckeThetaData.periodDualLattice_discrete (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    DiscreteTopology (D.periodDualLattice hg x) :=
  IntegralDualLattice.dualLattice_discrete _ (D.periodBasis hg x) _ (D.periodImaginaryForm_nondegenerate hg x)

instance Data.ActiveHeckeThetaData.periodDualLattice_full (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    IsZLattice ℝ (D.periodDualLattice hg x) :=
  IntegralDualLattice.dualLattice_full _ (D.periodBasis hg x) _ (D.periodImaginaryForm_nondegenerate hg x)

def Data.ActiveHeckeThetaData.periodDualLatticeEquiv (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    D.periodDualLattice hg x ≃ₗ[ℤ]
      ((D.canonicalPeriodData hg x).periodIntegerLattice →ₗ[ℤ] ℤ) :=
  IntegralDualLattice.integralDualLatticeEquiv _ (D.periodBasis hg x) _ (D.periodImaginaryForm_nondegenerate hg x)

theorem Data.ActiveHeckeThetaData.periodLattice_le_dual (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    (D.canonicalPeriodData hg x).periodIntegerLattice ≤ D.periodDualLattice hg x := by
  intro u hu v hv
  obtain ⟨a, ha⟩ := (D.periodLatticeEquiv hg x).surjective ⟨u, hu⟩
  obtain ⟨b, hb⟩ := (D.periodLatticeEquiv hg x).surjective ⟨v, hv⟩
  have he := D.periodImaginaryForm_integral hg x a b
  rw [ha, hb] at he
  exact Submodule.mem_one.mpr ⟨D.pel.reference.integralForm a b, he.symm⟩

end

end OAI.RepresentationTheory.Theta.Geometric

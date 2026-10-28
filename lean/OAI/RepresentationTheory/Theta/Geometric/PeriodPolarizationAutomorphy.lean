import OAI.RepresentationTheory.Theta.Geometric.PolarizationAutomorphy

/-! # Period Polarization Automorphy -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Polarization factors for the actual fixed reference lattice in
every period fiber, retaining the original integral form. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.referenceLatticePeriodEmbedding (x : D.domain) :
    D.pel.reference.lattice →+ Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) :=
  (D.periodReferenceEmbedding x.val).comp D.pel.reference.lattice.subtype.toAddMonoidHom

def Data.ActiveHeckeThetaData.periodPolarizationAutomorphy (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    D.pel.reference.lattice → Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) → ℂ :=
  PolarizationAutomorphy.polarizationAutomorphy (D.referenceBasis hg) D.pel.reference.integralForm
    (D.referenceLatticePeriodEmbedding x) (D.periodHermitian hg x)

theorem Data.ActiveHeckeThetaData.referenceIntegralForm_isAlt (hg : D.pel.HasIntegralModelGeometry) :
    D.pel.reference.integralForm.IsAlt := by
  rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, _, _, ha, _⟩
  exact ha

theorem Data.ActiveHeckeThetaData.periodHermitian_integral_embedding (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (l m : D.pel.reference.lattice) :
    (D.periodHermitian hg x (D.referenceLatticePeriodEmbedding x l)
      (D.referenceLatticePeriodEmbedding x m)).im = (D.pel.reference.integralForm l m : ℝ) :=
  D.periodImaginaryForm_integral hg x l m

theorem Data.ActiveHeckeThetaData.periodPolarizationAutomorphy_add (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (l m : D.pel.reference.lattice) (z : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.periodPolarizationAutomorphy hg x (l + m) z =
      D.periodPolarizationAutomorphy hg x l (z + D.referenceLatticePeriodEmbedding x m) *
        D.periodPolarizationAutomorphy hg x m z :=
  PolarizationAutomorphy.polarizationAutomorphy_add _ _ _ _ (D.referenceIntegralForm_isAlt hg)
    (D.periodHermitian_hermitian hg x) (D.periodHermitian_integral_embedding hg x) l m z

theorem Data.ActiveHeckeThetaData.periodPolarizationAutomorphy_poincare (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (l m : D.pel.reference.lattice) (w z : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.periodPolarizationAutomorphy hg x (l + m) (w + z) =
      D.periodPolarizationAutomorphy hg x l w * D.periodPolarizationAutomorphy hg x m z *
        Dual.PeriodProjectivity.poincareAutomorphy (D.periodHermitian hg x) (D.referenceLatticePeriodEmbedding x l)
          (D.referenceLatticePeriodEmbedding x m) w z :=
  PolarizationAutomorphy.polarizationAutomorphy_poincare _ _ _ _ (D.referenceIntegralForm_isAlt hg)
    (D.periodHermitian_hermitian hg x) (D.periodHermitian_integral_embedding hg x) l m w z

end

/-! The proved projective theta sections are sections of explicit
even powers of the original polarization factor. -/

section

variable {L I V : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L)
  (e : L →+ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

theorem PeriodPolarizationAutomorphy.polarizationAutomorphy_sq (l : L) (z : V) :
    PolarizationAutomorphy.polarizationAutomorphy b B e H l z ^ 2 = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H (e l) z := by
  rw [PolarizationAutomorphy.polarizationAutomorphy, pow_two, ← Complex.exp_add]
  unfold Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨LatticeSemicharacter.latticeQuadraticRefinement b B l, ?_⟩
  ring

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.periodThetaSection_translates (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) (n : ℕ)
    (t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection (D.periodHermitian hg x) (D.periodLattice x.val) n)
    (l : D.pel.reference.lattice) (z : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    t (z + D.referenceLatticePeriodEmbedding x l) =
      D.periodPolarizationAutomorphy hg x l z ^ (2 * n) * t z := by
  rw [pow_mul]
  have hs := PeriodPolarizationAutomorphy.polarizationAutomorphy_sq (D.referenceBasis hg) D.pel.reference.integralForm
    (D.referenceLatticePeriodEmbedding x) (D.periodHermitian hg x) l z
  change D.periodPolarizationAutomorphy hg x l z ^ 2 = _ at hs
  rw [hs]
  exact t.translates (D.periodLatticeMap x l) z

end

end OAI.RepresentationTheory.Theta.Geometric

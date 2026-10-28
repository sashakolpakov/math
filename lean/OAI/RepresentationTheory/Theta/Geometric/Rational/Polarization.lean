import OAI.RepresentationTheory.Theta.Geometric.Period.Hermitian
import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodCM

/-! # Polarization -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Rational SU transport preserves the prescribed trace polarization;
clearing by q^n multiplies it by q^(2n). -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.rationalLinear_traceForm (g : D.RationalSU) (u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    D.pel.reference.traceForm (D.rationalLinear g u) (D.rationalLinear g v) =
      D.pel.reference.traceForm u v := by
  have h : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian D.pel.reference.b (D.rationalLinear g u) (D.rationalLinear g v) =
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian D.pel.reference.b u v := g.property u v
  unfold AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.traceForm
  rw [h]

theorem Data.ActiveHeckeThetaData.rationalPeriodLinear_imaginary (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (u v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    (D.periodHermitian hg ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩
      (D.rationalPeriodLinear g x u) (D.rationalPeriodLinear g x v)).im =
        (D.periodHermitian hg x u v).im := by
  let y : D.domain := ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩
  let f := (D.rationalPeriodLinear g x).restrictScalars ℝ
  let B := (D.periodImaginaryForm hg y).compl₁₂ f f
  let C := D.periodImaginaryForm hg x
  have hs : Submodule.span ℝ (D.periodLattice x.val : Set (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s))) = ⊤ := by
    let : CompactSpace (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) ⧸ (D.periodLattice x.val).toIntSubmodule.toAddSubgroup) :=
      (D.periodLattice_geometry hg x).2.1
    exact CompactLattice.span_top_of_compact_quotient (D.periodLattice x.val).toIntSubmodule
  have hBC : B = C := by
    apply LinearMap.ext_on hs
    intro a ha
    apply LinearMap.ext_on hs
    intro b hb
    obtain ⟨a₀, _, rfl⟩ := (D.periodLattice_mem x.val a).mp ha
    obtain ⟨b₀, _, rfl⟩ := (D.periodLattice_mem x.val b).mp hb
    change (D.periodHermitian hg y
      (D.rationalPeriodLinear g x (D.periodReferenceEmbedding x.val a₀))
      (D.rationalPeriodLinear g x (D.periodReferenceEmbedding x.val b₀))).im =
        (D.periodHermitian hg x (D.periodReferenceEmbedding x.val a₀)
          (D.periodReferenceEmbedding x.val b₀)).im
    rw [D.rationalPeriodLinear_reference hg, D.rationalPeriodLinear_reference hg]
    change (D.periodHermitian hg y (D.periodReferenceEmbedding y.val (D.rationalLinear g a₀))
      (D.periodReferenceEmbedding y.val (D.rationalLinear g b₀))).im = _
    rw [D.periodHermitian_reference, D.periodHermitian_reference, D.rationalLinear_traceForm]
  exact DFunLike.congr_fun (DFunLike.congr_fun hBC u) v

theorem Data.ActiveHeckeThetaData.rationalPeriodLinear_hermitian (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (u v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.periodHermitian hg ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩
      (D.rationalPeriodLinear g x u) (D.rationalPeriodLinear g x v) = D.periodHermitian hg x u v := by
  apply Complex.ext
  · have h := D.rationalPeriodLinear_imaginary hg g x u (Complex.I • v)
    rw [map_smul, map_smul, map_smul] at h
    simpa only [smul_eq_mul, Complex.I_mul_im] using h
  · exact D.rationalPeriodLinear_imaginary hg g x u v

theorem Data.ActiveHeckeThetaData.cleared_rationalPeriodLinear_polarization (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (n : ℕ) (u v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.periodHermitian hg ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩
      (((q : ℤ) ^ n • D.rationalPeriodLinear g x) u)
      (((q : ℤ) ^ n • D.rationalPeriodLinear g x) v) = q ^ (2 * n) • D.periodHermitian hg x u v := by
  change D.periodHermitian hg _ ((q : ℤ) ^ n • D.rationalPeriodLinear g x u)
    ((q : ℤ) ^ n • D.rationalPeriodLinear g x v) = _
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply, smul_smul, ← pow_add,
    ← two_mul, D.rationalPeriodLinear_hermitian hg, ← Nat.cast_pow, natCast_zsmul]

end

end OAI.RepresentationTheory.Theta.Geometric

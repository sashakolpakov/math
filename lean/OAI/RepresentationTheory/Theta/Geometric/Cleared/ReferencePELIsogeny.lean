import OAI.RepresentationTheory.Theta.Geometric.PrescribedRationalIsogeny
import OAI.RepresentationTheory.Theta.Geometric.Rational.ClearedPeriods
import OAI.RepresentationTheory.Theta.Geometric.Cleared.ReferenceLevel
import OAI.RepresentationTheory.Theta.Geometric.Reference.IsogenyConstruction
import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliPoints
import OAI.RepresentationTheory.Theta.Geometric.Rational.Polarization

/-! # Reference PEL Isogeny -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Prescribed denominator clearing produces an actual original PEL
isogeny with the precise central marking shift and rational period map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.exists_cleared_reference_PEL_isogeny (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (g : D.RationalSU) (haway : D.away g ∈ D.awayLevel)
    (n : ℕ) (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) (R : D.ReferencePELPointData hg x)
    (S : D.ReferencePELPointData hg (D.rationalPeriodPoint g x)) :
    ∃ e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny R.family
        (S.family.shiftMarking (ZMod.unitOfCoprime (q ^ n) (hgood.2.2.1.pow_left n)))
        (q ^ (2 * n)),
      (∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.isogeny.hom (R.model.period t) =
        S.model.period (D.clearedPeriodTorusMap hg g n hn x t)) ∧
      ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.isogeny.hom ((R.model.toNativeReferenceModel R.analytic).nativeReferenceMarking v) =
          (S.model.toNativeReferenceModel S.analytic).nativeReferenceMarking
            ((q : ℤ) ^ n • D.rationalLinear g v) := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  obtain ⟨f, hmon, hfin, het, hsur, ha, hp⟩ :=
    D.exists_prescribed_rational_period_isogeny hg hc g haway n hn x R.model S.model
  let : IsMonHom f := hmon
  let : Etale f.left := het
  let i : R.model.abelianScheme.Isogeny S.model.abelianScheme :=
    { hom := f, preservesGroup := hmon, finite := hfin,
      flat := inferInstance, surjective := hsur }
  have hv (v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (R.model.period (QuotientAddGroup.mk v)) =
        S.model.period (QuotientAddGroup.mk ((q : ℤ) ^ n • D.rationalPeriodLinear g x v)) := hp _
  have hr (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := Data.ActiveHeckeThetaData.clearedReference_rationalPeriods hg g x
    R.analytic S.analytic n R.model S.model f hv v
  have he (u v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (R.model.toNativeReferenceModel R.analytic).abelian) :
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm (S.model.toNativeReferenceModel S.analytic).abelian S.polarization.ampleLine
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f u) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f v) =
        q ^ (2 * n) • AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm (R.model.toNativeReferenceModel R.analytic).abelian
          R.polarization.ampleLine u v := by
    have ht (w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f ((R.model.toNativeReferenceModel R.analytic).nativeReferenceMarking w) =
          (S.model.toNativeReferenceModel S.analytic).nativeReferenceMarking
            ((q ^ n : ℕ) • D.rationalLinear g w) := by
      simpa only [← Nat.cast_pow, natCast_zsmul] using hr w
    have H := Reference.MarkedChernSimilitude.reference_marked_chern_scaled_isometry R.polarization S.polarization f
      (q ^ n) (D.rationalLinear g) (D.rationalLinear_traceForm g) ht u v
    have hpow : q ^ n * q ^ n = q ^ (2 * n) := by rw [← pow_add, ← two_mul]
    rw [hpow] at H
    exact H
  have hl (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * (3 * s)) → ZMod D.pel.level))) :
      (R.family.marking.hom.app (.op T) c).val ≫ f =
        ((S.family.shiftMarking (ZMod.unitOfCoprime (q ^ n)
          (hgood.2.2.1.pow_left n))).marking.hom.app (.op T) c).val := by
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData.shiftMarking_q_points]
    exact D.algebraic_cleared_map_fixedLevel hgood hc g haway n hn R.model S.model
      R.analytic S.analytic f hp T c
  exact ⟨R.polarization.pelIsogeny_of_chern_similitude S.polarization D.pel.level
    (ZMod.unitOfCoprime (q ^ n) (hgood.2.2.1.pow_left n)) i (q ^ (2 * n)) he ha hl, hp, hr⟩

end

end OAI.RepresentationTheory.Theta.Geometric

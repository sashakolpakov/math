import OAI.RepresentationTheory.Theta.Geometric.Reference.LevelTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Marking

/-! # Reference Level -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A cleared rational SU map carries the complete fixed marking to
the actual scalar-shifted target marking over every complex test scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}

section

theorem Data.ActiveHeckeThetaData.PeriodModel.period_zero (M : D.PeriodModel hg x) : M.period 0 = 1 := by
  have h := M.period_add 0 0
  rw [zero_add] at h
  exact (mul_left_cancel ((mul_one (M.period 0)).trans h)).symm

theorem Data.ActiveHeckeThetaData.PeriodModel.period_nsmul (M : D.PeriodModel hg x) (n : ℕ)
    (t : (D.canonicalPeriodData hg x).periodTorus) : M.period (n • t) = M.period t ^ n := by
  induction n with
  | zero => simpa only [zero_smul, pow_zero] using M.period_zero
  | succ n hn => rw [succ_nsmul, M.period_add, hn, pow_succ]

end

variable (D)

theorem Data.ActiveHeckeThetaData.algebraic_cleared_map_fixedLevel
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hc : D.HasFiniteCoordinates)
    (g : D.RationalSU) (ha : D.away g ∈ D.awayLevel) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (M : D.PeriodModel hg x) (N : D.PeriodModel hg (D.rationalPeriodPoint g x))
    (F : D.ReferenceAnalyticFiber x) (G : D.ReferenceAnalyticFiber (D.rationalPeriodPoint g x))
    (f : M.abelian.toOver ⟶ N.abelian.toOver) [IsMonHom f]
    (hf : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      N.period (D.clearedPeriodTorusMap hg g n hn x t))
    (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (c : LocallyConstant T.left (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.Coefficients (3 * s) D.pel.level)) :
    ((M.fixedReferenceLevel F).hom.app (.op T) c).val ≫ f =
      ((N.fixedReferenceLevel G).hom.app (.op T) c).val ^ (q ^ n) := by
  have hqn : Nat.Coprime (q ^ n) D.pel.level := hgood.2.2.1.pow_left n
  let β : N.abelianScheme.FullLevel D.pel.level :=
    AlgebraicGeometry.AbelianScheme.TateComparison.Marking.levelScalarIso (3 * s) D.pel.level AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase (ZMod.unitOfCoprime (q ^ n) hqn) ≪≫
      N.fixedReferenceLevel G
  have hβ (U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
      (a : LocallyConstant U.left (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.Coefficients (3 * s) D.pel.level)) :
      (β.hom.app (.op U) a).val = ((N.fixedReferenceLevel G).hom.app (.op U) a).val ^ (q ^ n) := by
    change ((N.fixedReferenceLevel G).hom.app (.op U)
      ((AlgebraicGeometry.AbelianScheme.TateComparison.Marking.levelScalarIso (3 * s) D.pel.level AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase
        (ZMod.unitOfCoprime (q ^ n) hqn)).hom.app (.op U) a)).val = _
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.Marking.levelScalarIso_q_apply]
    exact congrArg Subtype.val (map_pow ((N.fixedReferenceLevel G).hom.app (.op U)).hom a (q ^ n))
  have hbase (a : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.Coefficients (3 * s) D.pel.level) :
      ((M.fixedReferenceLevel F).hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
        (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val ≫ f =
      (β.hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
        (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val := by
    obtain ⟨v, hv⟩ := D.pel.reference.fixedLevelLabel_surjective hg.reference_admissible D.pel.level a.toAdd
    have hv' : Multiplicative.ofAdd
        (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v) = a :=
      congrArg Multiplicative.ofAdd hv
    rw [hβ, ← hv', M.fixedReferenceLevel_period, N.fixedReferenceLevel_period]
    have hm := (hf (D.periodLevelPoint x v)).trans
      (congrArg N.period (D.clearedPeriodTorusMap_marking hg hgood hc g ha n hn x v))
    refine hm.trans ?_
    rw [← Nat.cast_pow, natCast_zsmul]
    exact N.period_nsmul (q ^ n) _
  exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.level_comparison_of_base_constants (M.fixedReferenceLevel F) β f hbase T c).trans
    (hβ T c)

theorem Data.ActiveHeckeThetaData.exists_algebraic_cleared_map_fixedLevel
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hc : D.HasFiniteCoordinates)
    (g : D.RationalSU) (ha : D.away g ∈ D.awayLevel) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (M : D.PeriodModel hg x) (N : D.PeriodModel hg (D.rationalPeriodPoint g x))
    (F : D.ReferenceAnalyticFiber x) (G : D.ReferenceAnalyticFiber (D.rationalPeriodPoint g x)) :
    ∃ f : M.abelian.toOver ⟶ N.abelian.toOver, IsMonHom f ∧
      (∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) = N.period (D.clearedPeriodTorusMap hg g n hn x t)) ∧
      ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
        (c : LocallyConstant T.left (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.Coefficients (3 * s) D.pel.level)),
        ((M.fixedReferenceLevel F).hom.app (.op T) c).val ≫ f =
          ((N.fixedReferenceLevel G).hom.app (.op T) c).val ^ (q ^ n) := by
  obtain ⟨f, hmon, hf⟩ := D.exists_algebraic_cleared_period_map hg g n hn x M.abelian N.abelian
    M.period N.period M.period_add N.period_add
  let : IsMonHom f := hmon
  exact ⟨f, hmon, hf, D.algebraic_cleared_map_fixedLevel hgood hc g ha n hn M N F G f hf⟩

end

end OAI.RepresentationTheory.Theta.Geometric

import OAI.RepresentationTheory.Theta.Geometric.IntegralRationalPeriodIso
import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodCM
import OAI.RepresentationTheory.Theta.Geometric.Reference.LevelTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers

/-! # Integral Rational Compatibility -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Integral rational SU maps preserve the actual CM action and, for
the original away-level condition, every ordered level section. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU)
    (hΛ : ∀ v, v ∈ D.pel.reference.lattice ↔ D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain)

include hΛ in
theorem Data.ActiveHeckeThetaData.integralRational_clearing_zero (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hv : v ∈ D.pel.reference.lattice) :
    (q : ℤ) ^ 0 • D.rationalLinear g v ∈ D.pel.reference.lattice := by
  simpa only [pow_zero, one_smul] using (hΛ v).mp hv

theorem Data.ActiveHeckeThetaData.integralRationalTorusMap_eq_cleared_zero :
    D.integralRationalTorusMap hg g hΛ x =
      D.clearedPeriodTorusMap hg g 0 (D.integralRational_clearing_zero g hΛ) x := by
  apply AddMonoidHom.ext
  intro t
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
  change QuotientAddGroup.mk (D.rationalPeriodLinear g x v) =
    QuotientAddGroup.mk (((q : ℤ) ^ 0 • D.rationalPeriodLinear g x) v)
  rw [pow_zero, one_smul]

theorem Data.ActiveHeckeThetaData.integralRationalTorusMap_marking
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hc : D.HasFiniteCoordinates)
    (haway : D.away g ∈ D.awayLevel) (v : D.pel.reference.lattice) :
    D.integralRationalTorusMap hg g hΛ x (D.periodLevelPoint x v) =
      D.periodLevelPoint (D.rationalPeriodPoint g x) v := by
  rw [D.integralRationalTorusMap_eq_cleared_zero]
  simpa only [pow_zero, one_smul] using D.clearedPeriodTorusMap_marking
    hg hgood hc g haway 0 (D.integralRational_clearing_zero g hΛ) x v

variable (M : D.PeriodModel hg x) (N : D.PeriodModel hg (D.rationalPeriodPoint g x))
    (f : M.abelian.toOver ⟶ N.abelian.toOver)
    (hf : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      N.period (D.integralRationalTorusMap hg g hΛ x t))

include hf in
theorem Data.ActiveHeckeThetaData.integralRational_action (a : NumberField.RingOfIntegers E) :
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.action a) ≫ f =
      f ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap N.abelian.toOver (N.action a) := by
  apply D.algebraic_cleared_period_map_CM hg g 0 (D.integralRational_clearing_zero g hΛ) x
    M.abelian N.abelian M.period N.period M.action N.action M.period_action N.period_action f
  intro t
  rw [← D.integralRationalTorusMap_eq_cleared_zero]
  exact hf t

include hf in
theorem Data.ActiveHeckeThetaData.integralRational_level [IsMonHom f]
    (F : D.ReferenceAnalyticFiber x) (G : D.ReferenceAnalyticFiber (D.rationalPeriodPoint g x))
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hc : D.HasFiniteCoordinates)
    (haway : D.away g ∈ D.awayLevel) (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (c : LocallyConstant T.left (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.Coefficients (3 * s) D.pel.level)) :
    ((M.fixedReferenceLevel F).hom.app (.op T) c).val ≫ f =
      ((N.fixedReferenceLevel G).hom.app (.op T) c).val := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.level_comparison_of_base_constants
    (A := M.abelianScheme) (B := N.abelianScheme)
    (M.fixedReferenceLevel F) (N.fixedReferenceLevel G) f
  intro a
  obtain ⟨v, hv⟩ := D.pel.reference.fixedLevelLabel_surjective hg.reference_admissible D.pel.level a.toAdd
  have ha : Multiplicative.ofAdd
      (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v) = a :=
    congrArg Multiplicative.ofAdd hv
  rw [← ha, M.fixedReferenceLevel_period, N.fixedReferenceLevel_period]
  exact (hf (D.periodLevelPoint x v)).trans
    (congrArg N.period (D.integralRationalTorusMap_marking hg g hΛ x hgood hc haway v))

end

end OAI.RepresentationTheory.Theta.Geometric

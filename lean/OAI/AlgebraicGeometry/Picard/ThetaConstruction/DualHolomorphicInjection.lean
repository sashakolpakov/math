import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LiftedGaugeTranslation
import OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

/-! # Dual Holomorphic Injection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

section

/-! A vanishing native holomorphic translation class reconstructs a
global holomorphic gauge. Unitary automorphy rigidity identifies its
parameter with the original integral dual lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationKernel_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationKernel_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationKernel_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

theorem PeriodModel.Geometric.AlgebraicPeriodModel.exists_translation_local_gauges (a : DefinitionsIntegral.Tangent dim)
    (ha : M.translationHolomorphicClass a = 0) :
    ∃ g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ,
      ∀ p r (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)),
        Complex.exp (M.localTranslationDifference a p r q) =
          (g r).val ⟨q.val, q.property.2⟩ / (g p).val ⟨q.val, q.property.1⟩ := by
  obtain ⟨g, hg⟩ := AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass.holomorphicUnitCech_trivialization_of_class_zero (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) M.localPeriodDomain
    (fun p => ⟨p, M.mem_localPeriodDomain p⟩) (M.translationUnitCech a) (M.translationUnitCech_closed a)
    ((M.translationUnitCech_class a).trans ha)
  refine ⟨g, ?_⟩
  intro p r q
  let b : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver := ![p, r]
  have hx : q.val ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b := by
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection M.localPeriodDomain b q.val).mpr
    intro i
    fin_cases i
    · exact q.property.1
    · exact q.property.2
  exact (M.translationUnitCech_value a b ⟨q.val, hx⟩).symm.trans (hg b ⟨q.val, hx⟩)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.exists_translation_global_gauge (a : DefinitionsIntegral.Tangent dim)
    (ha : M.translationHolomorphicClass a = 0) :
    ∃ c : (ProjectivePeriodData.Geometric.projectivePeriodData T).space → ℂ, Differentiable ℂ c ∧ (∀ w, c w ≠ 0) ∧
      ∀ (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) (w : (ProjectivePeriodData.Geometric.projectivePeriodData T).space),
        c (w + l.val) * Complex.exp ((Real.pi : ℂ) * T.riemannForm l.val a) = c w := by
  obtain ⟨g, hg⟩ := M.exists_translation_local_gauges a ha
  obtain ⟨c, hc⟩ := AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing.holomorphicFunction_global_glue (ProjectivePeriodData.Geometric.projectivePeriodData T).space (ProjectivePeriodData.Geometric.projectivePeriodData T).space
    M.liftedPeriodDomain M.liftedPeriodDomain_cover (M.liftedTranslationGauge a g)
    (M.liftedTranslationGauge_compatible a g hg)
  refine ⟨c, c.property.contDiff.differentiable (by simp), ?_, ?_⟩
  · intro w
    obtain ⟨p, hp⟩ := M.liftedPeriodDomain_cover w
    exact fun hz => M.liftedTranslationGauge_ne_zero a g p ⟨w, hp⟩ ((hc p ⟨w, hp⟩).symm.trans hz)
  · intro l w
    obtain ⟨p, hp⟩ := M.liftedPeriodDomain_cover w
    have hL := hc p ⟨w + l.val, (M.liftedPeriodDomain_translate p l w).mpr hp⟩
    have hR := hc p ⟨w, hp⟩
    exact (congrArg (fun t : ℂ => t * Complex.exp ((Real.pi : ℂ) * T.riemannForm l.val a)) hL).trans
      ((M.liftedTranslationGauge_translate a g p l ⟨w, hp⟩).trans hR.symm)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicClass_zero_mem_dual (a : DefinitionsIntegral.Tangent dim)
    (ha : M.translationHolomorphicClass a = 0) : a ∈ T.integralDualLattice := by
  obtain ⟨c, hc, hn, ht⟩ := M.exists_translation_global_gauge a ha
  let c₀ : DefinitionsIntegral.Tangent dim → ℂ := c
  have hc₀ : Differentiable ℂ c₀ := hc
  have hn₀ : ∀ w : DefinitionsIntegral.Tangent dim, c₀ w ≠ 0 := hn
  have ht₀ : ∀ (l : T.lattice) (w : DefinitionsIntegral.Tangent dim),
      c₀ (w + l.val) * Complex.exp ((Real.pi : ℂ) * T.riemannForm l.val a) = c₀ w := ht
  let : CompactSpace ((DefinitionsIntegral.Tangent dim) ⧸ T.lattice) := T.compact
  let : DiscreteTopology T.lattice := T.discrete
  have hshift : ∀ (l : T.lattice) w,
      RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge T.riemannForm a c₀ (w + l.val) =
        RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter T.riemannForm a l.val * RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge T.riemannForm a c₀ w := by
    intro l w
    have he : Complex.exp ((Real.pi : ℂ) * T.riemannForm a (w + l.val)) =
        Complex.exp ((Real.pi : ℂ) * T.riemannForm l.val a) *
          RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter T.riemannForm a l.val *
            Complex.exp ((Real.pi : ℂ) * T.riemannForm a w) := by
      simp only [RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter, ← Complex.exp_add, map_add]
      congr 1
      ring
    unfold RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge
    rw [he]
    calc
      _ = RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter T.riemannForm a l.val *
          (c₀ (w + l.val) * Complex.exp ((Real.pi : ℂ) * T.riemannForm l.val a)) *
            Complex.exp ((Real.pi : ℂ) * T.riemannForm a w) := by ac_rfl
      _ = _ := by rw [ht₀ l w, mul_assoc]
  intro v hv
  have hχ := RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity.unitaryAutomorphy_trivial T.lattice (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge T.riemannForm a c₀)
    (fun m => RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter T.riemannForm a m.val)
    (fun m => RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter_unitary _ T.hermitian a m.val)
    (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge_differentiable _ a c₀ hc₀) hshift
    (by simpa [RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge] using hn₀ 0) ⟨v, hv⟩
  obtain ⟨m, hm⟩ := (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter_eq_one_iff _ T.hermitian a v).mp hχ
  exact Submodule.mem_one.mpr ⟨m, hm.symm⟩

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicClass_zero_iff (a : DefinitionsIntegral.Tangent dim) :
    M.translationHolomorphicClass a = 0 ↔ a ∈ T.integralDualLattice :=
  ⟨M.translationHolomorphicClass_zero_mem_dual a, fun ha => M.translationHolomorphicClass_dual_zero ⟨a, ha⟩⟩

end

/-! The actual dual period torus embeds into the native holomorphic
Picard cohomology, with equality detected by the original dual lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.dualHolomorphicInjection_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.dualHolomorphicInjection_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.dualHolomorphicInjection_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicClass_eq_iff (a b : DefinitionsIntegral.Tangent dim) :
    M.translationHolomorphicClass a = M.translationHolomorphicClass b ↔ a - b ∈ T.integralDualLattice := by
  constructor
  · intro h
    exact (M.translationHolomorphicClass_zero_iff (a - b)).mp
      ((M.translationHolomorphicClass_sub a b).trans (sub_eq_zero.mpr h))
  · intro h
    exact sub_eq_zero.mp ((M.translationHolomorphicClass_sub a b).symm.trans
      ((M.translationHolomorphicClass_zero_iff (a - b)).mpr h))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.dualTorusHolomorphicHom_injective : Function.Injective M.dualTorusHolomorphicHom := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  apply (@QuotientAddGroup.eq_iff_sub_mem T.integralDualPeriodData.space inferInstance
    T.integralDualPeriodData.periodIntegerLattice.toAddSubgroup inferInstance a b).mpr
  exact (M.translationHolomorphicClass_eq_iff a b).mp h

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction

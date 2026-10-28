import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.LiftedGaugeTranslation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.TranslationRigidity

/-! # Dual Holomorphic Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

section

/-! A vanishing native holomorphic translation class reconstructs a
global holomorphic gauge. Unitary automorphy rigidity identifies its
parameter with the original integral dual lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.translationKernel_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.translationKernel_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.translationKernel_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

theorem AlgebraicModel.ReferenceAlgebraicModel.exists_translation_local_gauges (a : F.periodData.space)
    (ha : M.translationHolomorphicClass a = 0) :
    ∃ g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ,
      ∀ p r (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)),
        Complex.exp (M.localTranslationDifference a p r q) =
          (g r).val ⟨q.val, q.property.2⟩ / (g p).val ⟨q.val, q.property.1⟩ := by
  obtain ⟨g, hg⟩ := Intrinsic.HolomorphicIsoClass.holomorphicUnitCech_trivialization_of_class_zero (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
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

theorem AlgebraicModel.ReferenceAlgebraicModel.exists_translation_global_gauge (a : F.periodData.space)
    (ha : M.translationHolomorphicClass a = 0) :
    ∃ c : F.periodData.space → ℂ, Differentiable ℂ c ∧ (∀ w, c w ≠ 0) ∧
      ∀ (l : F.periodData.periodIntegerLattice) (w : F.periodData.space),
        c (w + l.val) * Complex.exp ((Real.pi : ℂ) * F.form l.val a) = c w := by
  obtain ⟨g, hg⟩ := M.exists_translation_local_gauges a ha
  obtain ⟨c, hc⟩ := Holomorphic.GlobalGluing.holomorphicFunction_global_glue F.periodData.space F.periodData.space
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
    exact (congrArg (fun t : ℂ => t * Complex.exp ((Real.pi : ℂ) * F.form l.val a)) hL).trans
      ((M.liftedTranslationGauge_translate a g p l ⟨w, hp⟩).trans hR.symm)

theorem AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicClass_zero_mem_dual (a : F.periodData.space)
    (ha : M.translationHolomorphicClass a = 0) : a ∈ F.dualLattice := by
  obtain ⟨c, hc, hn, ht⟩ := M.exists_translation_global_gauge a ha
  apply F.translationGauge_mem_dual hP a c hc (hn 0)
  intro l w
  have he := RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.polarizationAutomorphy_translate (P.referenceBasis hP) P.integralForm F.latticeEmbedding F.form l a w
  have htrans := ht (F.integralLatticeEquiv l) w
  have h : c (w + F.latticeEmbedding l) * Complex.exp ((Real.pi : ℂ) * F.form (F.latticeEmbedding l) a) = c w :=
    htrans
  calc
    _ = F.polarizationAutomorphy hP l w *
        (c (w + F.latticeEmbedding l) * Complex.exp ((Real.pi : ℂ) * F.form (F.latticeEmbedding l) a)) := by
      change c (w + F.latticeEmbedding l) * RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy (P.referenceBasis hP) P.integralForm
        F.latticeEmbedding F.form l (w + (show Fiber.ReferenceTangent s from a)) =
        RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy (P.referenceBasis hP) P.integralForm F.latticeEmbedding F.form l w *
          (c (w + F.latticeEmbedding l) * Complex.exp ((Real.pi : ℂ) * F.form (F.latticeEmbedding l) a))
      rw [he]
      ring
    _ = _ := congrArg (fun t => F.polarizationAutomorphy hP l w * t) h

theorem AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicClass_zero_iff (a : F.periodData.space) :
    M.translationHolomorphicClass a = 0 ↔ a ∈ F.dualLattice :=
  ⟨M.translationHolomorphicClass_zero_mem_dual a, fun ha => M.translationHolomorphicClass_dual_zero ⟨a, ha⟩⟩

end

/-! The actual dual period torus embeds into the native holomorphic
Picard cohomology, with equality detected by the original dual lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.dualHolomorphicInjection_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.dualHolomorphicInjection_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.dualHolomorphicInjection_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

theorem AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicClass_eq_iff (a b : F.periodData.space) :
    M.translationHolomorphicClass a = M.translationHolomorphicClass b ↔ a - b ∈ F.dualLattice := by
  constructor
  · intro h
    exact (M.translationHolomorphicClass_zero_iff (a - b)).mp
      ((M.translationHolomorphicClass_sub a b).trans (sub_eq_zero.mpr h))
  · intro h
    exact sub_eq_zero.mp ((M.translationHolomorphicClass_sub a b).symm.trans
      ((M.translationHolomorphicClass_zero_iff (a - b)).mpr h))

theorem AlgebraicModel.ReferenceAlgebraicModel.dualTorusHolomorphicHom_injective : Function.Injective M.dualTorusHolomorphicHom := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  apply (@QuotientAddGroup.eq_iff_sub_mem (F.dualPeriodData hP).space inferInstance
    (F.dualPeriodData hP).periodIntegerLattice.toAddSubgroup inferInstance a b).mpr
  exact (M.translationHolomorphicClass_eq_iff a b).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

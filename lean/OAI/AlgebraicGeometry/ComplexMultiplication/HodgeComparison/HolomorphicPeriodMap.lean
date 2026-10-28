import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodProjectionHolomorphic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodMapGluing

/-! # Holomorphic Period Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPeriodMap.CM.Construction

noncomputable section

/-! Every rational H¹ basis gives an actual holomorphic map to its
compact complex period quotient, with the computed local differential. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient

theorem mdifferentiable_of_open_restrictions
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
    (f : M → N)
    (hf : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) (fun y : U => f y.val)) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f := by
  intro x
  obtain ⟨U, hx, hU⟩ := hf x
  let hs : Nonempty U := ⟨⟨x, hx⟩⟩
  let e := U.openPartialHomeomorphSubtypeCoe hs
  have hg := (hU (e.symm x)).comp x
    ((Intersection.CM.Construction.complexOpenInverse_contMDiffAt U hs hx).mdifferentiableAt (by simp))
  have heq : ((fun y : U => f y.val) ∘ e.symm) =ᶠ[𝓝 x] f := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact congrArg f (e.right_inv (by
      simpa only [e, Opens.openPartialHomeomorphSubtypeCoe_target] using hy))
  exact heq.mdifferentiableAt_iff.mp hg

theorem exists_holomorphic_rationalH1_period_map (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1)) :
    ∃ d : ℤ, 0 < d ∧ ∃ p : C(V.analyticSpace, PeriodLattice.CM.Construction.RationalH1PeriodTorus V b),
      MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) p ∧
      ∀ x : V.analyticSpace, ∃ U : Opens V.analyticSpace, x ∈ U ∧
        ∃ f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel U 0,
          (∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) =
            d • Intersection.CM.Construction.restrictSmoothForm U 1 (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val) ∧
          ∀ y : U, p y.val = QuotientAddGroup.mk
            (PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) y)) := by
  let L := (PeriodLattice.CM.Construction.rationalPeriodProjection V b).toLinearMap.toAddMonoidHom
  obtain ⟨d, hd, p, hlocal⟩ := PeriodMapGluing.CM.Construction.projective_period_map V (fun i => b i)
    (fun i => CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i))
    (fun i => CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative_class V (b i))
    L (PeriodLattice.CM.Construction.rationalPeriodProjection V b).continuous (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
    (PeriodLattice.CM.Construction.rationalPeriodProjection_integer_mem V b)
  refine ⟨d, hd, p, ?_, hlocal⟩
  apply mdifferentiable_of_open_restrictions
  intro x
  obtain ⟨U, hx, f, hf, hp⟩ := hlocal x
  refine ⟨U, hx, ?_⟩
  have hF := PeriodProjectionHolomorphic.CM.Construction.rationalPeriodProjection_primitives_holomorphic V b U d f hf
  have hπ := (QuotientManifold.CM.Construction.ComplexLatticeQuotient.projection_contMDiff
    (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup).mdifferentiable (by simp)
  have hcomp := hπ.comp hF
  have heq : (fun y : U => p y.val) = fun y : U =>
      (QuotientAddGroup.mk
        (PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) y)) : PeriodLattice.CM.Construction.RationalH1PeriodTorus V b) :=
    funext hp
  rw [heq]
  exact hcomp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPeriodMap.CM.Construction

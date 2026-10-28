import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalWinding
import OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD
import OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledChainSupport

/-! # Integral Residue Evaluation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralResidueEvaluation

noncomputable section

section

/-!
# ChernClass: integrality of the actual winding residue

The winding cochain has integer simplex values. Zero extension and the
ordinary differential preserve this lattice. Consequently its relative class
has integral evaluation on every genuine integral relative homology class,
including the existing geometric normal generator.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledChainSupport.Cycles OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The actual integers inside the rational coefficient module. -/
def integerLattice : Submodule ℤ AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalIntegralCoefficient :=
  LinearMap.range (LinearMap.toSpanSingleton ℤ ℚ (1 : ℚ))

theorem mem_integerLattice_iff (q : ℚ) : q ∈ integerLattice ↔ ∃ m : ℤ, (m : ℚ) = q := by
  change (∃ m : ℤ, m • (1 : ℚ) = q) ↔ _
  simp only [zsmul_eq_mul, mul_one]

/-- A genuine rational cochain with integer values on all actual simplices. -/
def CochainIntegral (X : TopCat.{0}) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n) : Prop :=
  ∀ s : (TopCat.toSSet.obj X) _⦋n⦌,
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) n).hom c s ∈ integerLattice

/-- The original winding construction uses actual integral logarithmic defects. -/
theorem singularWindingCochain_integral (X : TopCat.{0}) (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0) :
    CochainIntegral X 1 (WindingSingular.singularWindingCochain X g hg) := by
  intro s
  rw [WindingSingular.singularWindingCochain_value, mem_integerLattice_iff]
  exact ⟨_, rfl⟩

/-- Extending by zero preserves the actual integral lattice. -/
theorem zeroExtendCochain_integral (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of A)).X n)
    (hc : CochainIntegral (TopCat.of A) n c) : CochainIntegral X n (SubspaceCechD.zeroExtendCochain X A n c) := by
  classical
  intro s
  rw [SubspaceCechD.zeroExtendCochain_value, Function.extend_def]
  split_ifs with h
  · exact hc h.choose
  · exact integerLattice.zero_mem

/-- The actual alternating singular differential preserves integral simplex values. -/
theorem CochainIntegral.d {X : TopCat.{0}} {n : ℕ}
    {c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n} (hc : CochainIntegral X n c) :
    CochainIntegral X (n + 1) ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n + 1) c) := by
  intro s
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_coboundary]
  apply Submodule.sum_mem
  intro i _
  exact integerLattice.smul_mem _ (hc _)

/-- Integral simplex values give integral evaluation on every actual integral chain. -/
theorem CochainIntegral.evaluate {X : TopCat.{0}} {n : ℕ}
    {c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n} (hc : CochainIntegral X n c)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n c z ∈ integerLattice := by
  apply CycleClass.Geometric.ControlledChainSupport.Cycles.singularLinearMap_mem_one X n AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalIntegralCoefficient integerLattice _ _ z
  intro s
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n c
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) ∈ integerLattice
  rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_simplex,
    ← AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) c s]
  exact hc s

/-- A relative cochain whose absolute simplex values are integral evaluates
integrally on every actual integral relative chain. -/
theorem relativeIntegral_evaluate (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n)
    (hc : CochainIntegral X n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n c))
    (z : (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n) :
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X A n c z ∈ integerLattice := by
  obtain ⟨z, rfl⟩ := CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective ℤ X A n z
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X A n c ((CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n z) ∈ integerLattice
  rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv_projection]
  exact hc.evaluate z

/-- The actual relative winding cocycle retains its integral coefficients. -/
theorem relativeWindingCocycle_integral (X : TopCat.{0}) (A : Set X)
    (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0) :
    CochainIntegral X 2 ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f 2
      (SubspaceCechD.relativeWindingCocycle X A g hg).val) := by
  change CochainIntegral X 2 ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f 2
    (SubspaceCechD.zeroExtensionConnectingCocycle X A 1 (WindingSingular.singularWindingCocycle (TopCat.of A) g hg)).val)
  rw [SubspaceCechD.zeroExtensionConnectingCocycle_inclusion]
  exact (zeroExtendCochain_integral X A 1 (WindingSingular.singularWindingCochain (TopCat.of A) g hg)
    (singularWindingCochain_integral (TopCat.of A) g hg)).d

/-- The supported winding class pairs integrally with all integral relative homology. -/
theorem supportedWindingClass_integralEvaluation (X : TopCat.{0}) (A : Set X)
    (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0) (z : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A 2) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X A 2 (Supported.Winding.supportedWindingClass X A g hg) z ∈ integerLattice := by
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) 2 z
  rw [← SubspaceCechD.relativeWindingCocycle_class, AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class]
  exact relativeIntegral_evaluate X A 2 (SubspaceCechD.relativeWindingCocycle X A g hg).val
    (relativeWindingCocycle_integral X A g hg) z.val

/-- The previously defined comparison coefficient is an integer, with its
sign still determined by the independent geometric orientation convention. -/
theorem normalWindingCoefficient_integral : ∃ m : ℤ, (m : ℚ) = NormalWinding.normalWindingCoefficient := by
  have h := supportedWindingClass_integralEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured
    NormalWinding.normalPuncturedCoordinate NormalWinding.normalPuncturedCoordinate_ne_zero ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1)
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2
    NormalWinding.normalSupportedWindingClass ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1) ∈ integerLattice at h
  rw [NormalWinding.normalSupportedWindingClass_eq_coefficient_smul, map_smul] at h
  change NormalWinding.normalWindingCoefficient * AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1) ∈ integerLattice at h
  rw [AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.complexNormalRationalDualClass_integralEvaluation, mul_one] at h
  exact (mem_integerLattice_iff _).mp h

end

/-! Boundary evaluation of the actual winding residue on integral relative chains. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledChainSupport.Cycles OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) (A : Set X)

/-- An integral absolute filling gives an integral relative cycle. -/
theorem integralRelativeProjection_cycle_of_boundary
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X 2) (u : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X 1)
    (hu : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d 2 1 z = (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f 1 u) :
    (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f 2 z ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) 2 := by
  rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
  have h := ConcreteCategory.congr_hom ((CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).comm 2 1) z
  change (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d 2 1 ((CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f 2 z) =
    (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f 1 ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d 2 1 z) at h
  rw [hu] at h
  exact h.trans (ConcreteCategory.congr_hom
    (congrArg (fun f => f.f 1) (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection ℤ X A)) u)

/-- The integral relative pairing computes the actual boundary winding, with its fixed sign. -/
theorem supportedWindingClass_integralBoundaryEvaluation (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X 2) (u : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X 1)
    (hu : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d 2 1 z = (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f 1 u) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X A 2 (Supported.Winding.supportedWindingClass X A g hg)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) 2
        ⟨(CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f 2 z, integralRelativeProjection_cycle_of_boundary X A z u hu⟩) =
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj (TopCat.of A)) 1
      (WindingSingular.singularWindingCochain (TopCat.of A) g hg) u := by
  rw [← SubspaceCechD.relativeWindingCocycle_class, AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class,
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv_projection]
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) 2
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f 2
        (SubspaceCechD.zeroExtensionConnectingCocycle X A 1 (WindingSingular.singularWindingCocycle (TopCat.of A) g hg)).val) z = _
  rw [SubspaceCechD.zeroExtensionConnectingCocycle_inclusion]
  have hd := LinearMap.congr_fun (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_d (TopCat.toSSet.obj X) 1 2
    (SubspaceCechD.zeroExtendCochain X A 1 (WindingSingular.singularWindingCochain (TopCat.of A) g hg))) z
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) 2
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 1 2
        (SubspaceCechD.zeroExtendCochain X A 1 (WindingSingular.singularWindingCochain (TopCat.of A) g hg))) z =
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) 1
      (SubspaceCechD.zeroExtendCochain X A 1 (WindingSingular.singularWindingCochain (TopCat.of A) g hg))
      ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d 2 1 z) at hd
  rw [hu] at hd
  have hr := LinearMap.congr_fun (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_pullback
    (TopCat.toSSet.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)) 1
    (SubspaceCechD.zeroExtendCochain X A 1 (WindingSingular.singularWindingCochain (TopCat.of A) g hg))) u
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj (TopCat.of A)) 1
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f 1
        (SubspaceCechD.zeroExtendCochain X A 1 (WindingSingular.singularWindingCochain (TopCat.of A) g hg))) u =
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) 1
      (SubspaceCechD.zeroExtendCochain X A 1 (WindingSingular.singularWindingCochain (TopCat.of A) g hg))
      ((CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f 1 u) at hr
  rw [SubspaceCechD.zeroExtendCochain_restrict] at hr
  exact hd.trans hr.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralResidueEvaluation

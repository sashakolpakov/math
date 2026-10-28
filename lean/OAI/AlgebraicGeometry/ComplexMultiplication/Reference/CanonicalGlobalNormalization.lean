import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceCanonicalComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntegrationCriterion
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.BettiBridge

/-! # Canonical Global Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalGlobalNormalization

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # The original global comparison has the native canonical normalization

Scalar forgetting and extension by zero retain the actual integration maps.
No comparison diagram is supplied as a mathematical premise.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

local notation "F" => forget₂ (ModuleCat ℂ) AddCommGrpCat
local notation "FN" => Functor.mapHomologicalComplex
  (forget₂ (ModuleCat ℂ) AddCommGrpCat) (ComplexShape.up ℕ)

/-- Forgetting scalars and extending by zero retain the actual natural-degree cohomology. -/
def moduleIntegerAdditiveHomologyIso (K : CochainComplex (ModuleCat ℂ) ℕ) (n : ℕ) :
    (((FN).obj K).extend ComplexShape.embeddingUpNat).homology (n : ℤ) ≅
      (F).obj (K.homology n) :=
  ((FN).obj K).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    (K.sc n).mapHomologyIso (F)

set_option backward.isDefEq.respectTransparency false in
/-- This cohomology identification is natural in the actual complex map. -/
theorem moduleIntegerAdditiveHomologyIso_square
    {K L : CochainComplex (ModuleCat ℂ) ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap ((FN).map f) ComplexShape.embeddingUpNat) (n : ℤ) ≫
          (moduleIntegerAdditiveHomologyIso L n).hom =
      (moduleIntegerAdditiveHomologyIso K n).hom ≫
        (F).map (HomologicalComplex.homologyMap f n) := by
  dsimp only [moduleIntegerAdditiveHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, HomologicalComplex.extendHomologyIso_hom_naturality,
    Category.assoc, SingularDualMap.forgottenModuleComplex_homology_naturality]
  exact (Category.assoc _ _ _).symm

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "A" => ModuleCat.of ℂ ℂ
local notation "DR" => OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "SC" => OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains
  (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) (ModuleCat.of ℂ ℂ) (ComplexPoint.Basic.ComplexSchemePoint X)
local notation "IO" => OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap
  (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) (ComplexPoint.Basic.ComplexSchemePoint X)
local notation "RO" => OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction
  (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) (ModuleCat.of ℂ ℂ) (ComplexPoint.Basic.ComplexSchemePoint X)

/-- The actual original-atlas de Rham cohomology with its integer additive indexing. -/
def originalManifoldIntegerDeRhamCohomologyIso (n : ℕ) :
    (ReferenceSmooth.GlobalForms.originalManifoldDeRhamComplexInt X).homology (n : ℤ) ≅
      (F).obj (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M n) :=
  moduleIntegerAdditiveHomologyIso (DR) n

/-- The actual original smooth-singular cohomology with its integer additive indexing. -/
def originalManifoldIntegerSmoothCohomologyIso (n : ℕ) :
    (GlobalIntegrationClasses.originalManifoldSmoothCochainsInt X).homology (n : ℤ) ≅
      (F).obj ((SC).homology n) :=
  moduleIntegerAdditiveHomologyIso (SC) n

set_option backward.isDefEq.respectTransparency false in
/-- Actual integer-indexed simplex integration retains its original module cohomology map. -/
theorem originalManifoldIntegerIntegration_normalization (n : ℕ)
    (z : (ReferenceSmooth.GlobalForms.originalManifoldDeRhamComplexInt X).homology (n : ℤ)) :
    (originalManifoldIntegerSmoothCohomologyIso X n).hom
        (HomologicalComplex.homologyMap (GlobalIntegrationClasses.originalManifoldSimplexIntegrationInt X) (n : ℤ) z) =
      HomologicalComplex.homologyMap (IO) n
        ((originalManifoldIntegerDeRhamCohomologyIso X n).hom z) :=
  ConcreteCategory.congr_hom (moduleIntegerAdditiveHomologyIso_square (IO) n) z

set_option backward.isDefEq.respectTransparency false in
/-- Actual integer-indexed smooth restriction retains its original module cohomology map. -/
theorem originalManifoldIntegerRestriction_normalization (n : ℕ)
    (z : (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ)) :
    (originalManifoldIntegerSmoothCohomologyIso X n).hom
        (HomologicalComplex.homologyMap (OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) (n : ℤ) z) =
      HomologicalComplex.homologyMap (RO) n
        ((CanonicalSingularGlobalClasses.originalOrdinaryAmbientIntegerCohomologyIso X n).hom z) :=
  ConcreteCategory.congr_hom (moduleIntegerAdditiveHomologyIso_square (RO) n) z

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

omit [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
/-- The ordinary cohomology identity is the same actual point-space pullback as the Betti bridge. -/
theorem nativeOriginalOrdinaryCohomologyIso_hom_pullback (n : ℕ) :
    (IntrinsicReferenceCanonicalComparison.nativeOriginalOrdinaryCohomologyIso X n).hom =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback A (PointBettiBridge.complexPointSpaceIso X).inv n := by
  change HomologicalComplex.homologyMap (IntrinsicReferenceAtlasComparison.nativeOriginalOrdinaryCochainComplexIso X).hom n = _
  rw [IntrinsicReferenceAtlasComparison.nativeOriginalOrdinaryCochainComplexIso_hom_eq]
  rfl

/-- A genuine scheme Betti class in the original integer-indexed ordinary complex. -/
def originalOrdinaryIntegerClass (n : ℕ) (z : Betti.Scheme.schemeBetti A X n) :
    (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ) :=
  (CanonicalSingularGlobalClasses.originalOrdinaryAmbientIntegerCohomologyIso X n).addCommGroupIsoToAddEquiv.symm
    ((IntrinsicReferenceCanonicalComparison.nativeOriginalOrdinaryCohomologyIso X n).hom z)

set_option backward.isDefEq.respectTransparency false in
/-- This is precisely the original constant-sheaf Betti comparison, on the same class. -/
theorem originalOrdinaryIntegerClass_constant (n : ℕ) (z : Betti.Scheme.schemeBetti A X n) :
    ReferenceSmooth.GlobalClassComparison.originalOrdinaryConstantCohomologyAddEquiv X n (originalOrdinaryIntegerClass X n z) =
      BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n z := by
  have hb : CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℂ X n
      (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ (TopCat.of M) n
        ((IntrinsicReferenceCanonicalComparison.nativeOriginalOrdinaryCohomologyIso X n).hom z)) =
      BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n z := by
    rw [nativeOriginalOrdinaryCohomologyIso_hom_pullback]
    rfl
  simpa only [ReferenceSmooth.GlobalClassComparison.originalOrdinaryConstantCohomologyAddEquiv, originalOrdinaryIntegerClass,
    AddEquiv.trans_apply, AddEquiv.apply_symm_apply, LinearEquiv.coe_toAddEquiv] using! hb

set_option backward.isDefEq.respectTransparency false in
/-- The original holomorphic global class equals the canonical comparison exactly on actual forms. -/
theorem originalCanonicalDeRhamGlobalClass_iff (n : ℕ)
    (a : (V).deRhamCohomology n)
    (w : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of M) Ω•(X)).homology (n : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
        ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
          (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n (((V).deRhamBettiIso n).hom a))) =
      GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) (n : ℤ) w ↔
    (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X n).hom a =
      (originalManifoldIntegerDeRhamCohomologyIso X n).hom
        (HomologicalComplex.homologyMap (GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (n : ℤ) w) := by
  rw [← originalOrdinaryIntegerClass_constant]
  rw [IntegrationCriterion.originalOrdinaryDeRhamGlobalClass_iff]
  have hs : Function.Injective (originalManifoldIntegerSmoothCohomologyIso X n).hom :=
    (originalManifoldIntegerSmoothCohomologyIso X n).addCommGroupIsoToAddEquiv.injective
  rw [← hs.eq_iff, originalManifoldIntegerRestriction_normalization,
    originalManifoldIntegerIntegration_normalization]
  have hi := (CanonicalSingularGlobalClasses.originalOrdinaryAmbientIntegerCohomologyIso X n).addCommGroupIsoToAddEquiv.apply_symm_apply
      ((IntrinsicReferenceCanonicalComparison.nativeOriginalOrdinaryCohomologyIso X n).hom (((V).deRhamBettiIso n).hom a))
  simp only [Iso.addCommGroupIsoToAddEquiv_apply] at hi
  dsimp only [originalOrdinaryIntegerClass]
  rw [hi]
  exact (IntrinsicReferenceCanonicalComparison.nativeOriginalCanonicalComparison_iff X n a _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Original F¹ has exactly the actual native canonical closed-holomorphic-form criterion. -/
theorem originalF1_mem_iff_nativeCanonicalForm (a : (V).deRhamCohomology 1) :
    ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X 1
        ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X 1).symm
          (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X 1 (((V).deRhamBettiIso 1).hom a))) ∈
        ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 ↔
      ∃ (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).presheaf.obj (Opposite.op ⊤))
        (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).hom.app (Opposite.op ⊤) θ = 0),
        (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).hom a =
          (originalManifoldIntegerDeRhamCohomologyIso X 1).hom
            (HomologicalComplex.homologyMap (GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) 1
              (ClosedHolomorphicClasses.originalClosedHolomorphicGlobalClass X 1 θ hθ)) := by
  rw [ClosedGlobalRepresentatives.originalF1_mem_iff_closedGlobalSection]
  constructor
  · rintro ⟨θ, hθ, he⟩
    exact ⟨θ, hθ, (originalCanonicalDeRhamGlobalClass_iff X 1 a _).mp he.symm⟩
  · rintro ⟨θ, hθ, he⟩
    exact ⟨θ, hθ, ((originalCanonicalDeRhamGlobalClass_iff X 1 a _).mpr he).symm⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalGlobalNormalization

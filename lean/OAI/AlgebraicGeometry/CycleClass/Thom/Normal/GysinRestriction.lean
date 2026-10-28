import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceOpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.MapDegreeSupport

/-! # Gysin Restriction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions

/-! The original global Gysin isomorphism, with an arbitrary closed
support in the immersion image, restricts to the actual local normal
equation Gysin isomorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceOpenNaturality.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions.Support OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions
  RetractionComparison.Constructions Relative.MapDegreeSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (W : Opens V.analyticSpace) (hW : (W : Set V.analyticSpace)ᶜ ⊆ Set.range Z.regularComplementInclusion)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def globalGysinIso (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Z.regularAnalyticSpace
      (Z.regularComplementInclusion ⁻¹' (W : Set V.analyticSpace)) (2 * q) ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace (W : Set V.analyticSpace) (2 * (p + q)) :=
  Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha W (2 * q) ≪≫
    eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr V.analyticSpace (GysinLocalIso.Constructions.Support.globalTargetComplement Z W hW) (2 * (p + q))

variable (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)
  (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ))
  (hg : ∀ y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding,
    g y = 0 ↔ Z.regularComplementInclusion y.val ∉ W)

include hg in
theorem sourceMapsTo : Set.MapsTo
    (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
    (RetractionComparison.Constructions.sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding))
    (Z.regularComplementInclusion ⁻¹' (W : Set V.analyticSpace)) := by
  intro y hy
  exact (Set.ext_iff.mp (GysinLocalIso.Constructions.Support.sourceComplement Z x P W g hg) y).mpr hy

theorem globalGysinIso_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
      (sourceMapsTo Z W x P g hg) (2 * q) ≫
      (GysinLocalIso.Constructions.localGysinIso Z x P W hW g hg a ha).hom =
    (globalGysinIso Z W hW a ha q).hom ≫
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
        (W : Set V.analyticSpace) P.openNeighborhood (2 * (p + q)) := by
  let s₁ := Iso.refl (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Z.regularAnalyticSpace
    (Z.regularComplementInclusion ⁻¹' (W : Set V.analyticSpace)) (2 * q))
  let s₂ := AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr
    (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) (GysinLocalIso.Constructions.Support.sourceComplement Z x P W g hg) (2 * q)
  let t₁ := eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr V.analyticSpace (GysinLocalIso.Constructions.Support.globalTargetComplement Z W hW) (2 * (p + q))
  let t₂ := eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
        ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) P.openNeighborhood) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of P.neighborhood) (GysinLocalIso.Constructions.targetEquality Z x P W hW) (2 * (p + q))
  have hs := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality
    (Geometric.LocalHomology.Cycles.subspaceInclusion Z.regularAnalyticSpace
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding : Set Z.regularAnalyticSpace))
    (GysinLocalIso.Constructions.Support.sourceComplement Z x P W g hg) (rfl : Z.regularComplementInclusion ⁻¹' (W : Set V.analyticSpace) = _)
    (fun _ hx => hx) (sourceMapsTo Z W x P g hg) (2 * q)
  have ht := Relative.MapDegreeSupport.Constructions.relativePairMap_degreeSupport
    (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (P.openNeighborhood : Set V.analyticSpace))
    (GysinLocalIso.Constructions.targetEquality Z x P W hW) (GysinLocalIso.Constructions.Support.globalTargetComplement Z W hW) (fun _ hx => hx) (fun _ hx => hx)
    (Nat.mul_add 2 p q).symm
  have hn := Immersion.GlobalSourceOpenNaturality.Constructions.Construction.regularSourceThomSupportedGlobalIso_open_naturality Z a ha W P.openNeighborhood (2 * q)
  have h := Immersion.SupportedSourceNaturality.Constructions.Construction.sourceTargetIso_naturality s₁ s₂
    (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha W (2 * q))
    (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha W P.openNeighborhood (2 * q)) t₁ t₂ _ _ _ _ hs hn ht
  simpa only [s₁, s₂, t₁, t₂, globalGysinIso, GysinLocalIso.Constructions.localGysinIso, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction,
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, Iso.trans_hom, Iso.symm_hom, Iso.refl_inv,
    Category.id_comp, Category.assoc] using h

end AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions.ThomClass

/-! On a neighborhood where an arbitrary closed support is a smooth
submanifold defined by a source submersion, its local Gysin class is
the genuine Thom class of that support. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions.Support OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions
  RetractionComparison.Constructions Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)
  (W : Opens V.analyticSpace) (hW : (W : Set V.analyticSpace)ᶜ ⊆ Set.range Z.regularComplementInclusion)
  (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ))
  (hg : ∀ y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding,
    g y = 0 ↔ Z.regularComplementInclusion y.val ∉ W)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V P.openNeighborhood) (p + q))
  (hC : Set.range C.regularComplementInclusion = Subtype.val ⁻¹' (W : Set V.analyticSpace)ᶜ)

include hC in
theorem supportEquality :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace) (W : Set V.analyticSpace) P.openNeighborhood =
      (Set.range C.regularComplementInclusion)ᶜ := by
  ext y
  change y.val ∈ W ↔ y ∉ Set.range C.regularComplementInclusion
  rw [hC]
  exact not_not.symm

variable
  (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
    𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)))
  (hPa : ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) ω
    P.ambientChart P.ambientChart.source)
  (hPi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) 𝓘(ℂ, V.analyticModel) ω
    P.ambientChart.symm P.ambientChart.target)
  (hga : ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) ω g)
  (hgs : ∀ y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding, g y = 0 →
    Function.Surjective (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) g y))
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

include hP hPa hPi hga hgs

theorem localGysinIso_normalClass :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood) A (2 * (p + q))) (supportEquality Z x P W C hC))
      ((GysinLocalIso.Constructions.localGysinIso Z x P W hW g hg a ha).hom
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g
          (A := (RetractionComparison.Constructions.sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)))
          (B := {0}ᶜ) (fun _ hx => hx) (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q))) =
    C.regularThomClass := by
  have hCg : Set.range C.regularComplementInclusion =
      (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding) '' (g ⁻¹' {0}) :=
    hC.trans (GysinLocalIso.Constructions.Support.normalZero_image Z x P W hW g hg).symm
  have hn := RetractionComparison.Constructions.normalRetractionThomIso_eq_Thom Z x P C g hCg hP hPa hPi hga hgs a ha
  rw [GysinLocalIso.Constructions.localGysinIso_eq_retraction]
  simp only [Iso.trans_hom, AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr,
    eqToIso.hom, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply, eqToHom_trans]
  exact hn

end AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions.ThomClass

end

end OAI

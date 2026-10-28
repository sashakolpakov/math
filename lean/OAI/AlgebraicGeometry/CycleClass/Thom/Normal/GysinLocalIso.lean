import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionZeroLocus
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionComparison
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RetractionComparison

/-! # Gysin Local Iso -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions.Support

/-! In a genuine outer normal neighborhood, a source equation for
an arbitrary closed subset has exactly the support required by the
original Gysin construction. No global smoothness of that subset is used. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionZeroLocus.Constructions
  RetractionComparison.Constructions Immersion.Retraction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)
  (W : Opens V.analyticSpace) (hW : (W : Set V.analyticSpace)ᶜ ⊆ Set.range Z.regularComplementInclusion)
  (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ))
  (hg : ∀ y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding,
    g y = 0 ↔ Z.regularComplementInclusion y.val ∉ W)

include hW in
theorem globalTargetComplement :
    ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) = W := by
  apply Set.union_eq_right.mpr
  intro y hy
  by_contra hn
  exact hy (hW hn)

include hg in
theorem sourceComplement :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Z.regularAnalyticSpace)
      (((Opens.map (Immersion.SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj W) : Set Z.regularAnalyticSpace)
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) =
    (RetractionComparison.Constructions.sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) := by
  ext y
  change Z.regularComplementInclusion y.val ∈ W ↔ g y ≠ 0
  simpa only [not_not] using (not_congr (hg y)).symm

include hW hg in
theorem normalZero_image :
    (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding) '' (g ⁻¹' {0}) =
      Subtype.val ⁻¹' (W : Set V.analyticSpace)ᶜ := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (hg t).mp ht
  · intro hy
    obtain ⟨t, ht⟩ := hW hy
    let t' : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding := ⟨t, by
      change Z.regularComplementInclusion t ∈ P.neighborhood
      rw [ht]
      exact y.property⟩
    refine ⟨t', (hg t').mpr ?_, ?_⟩
    · change Z.regularComplementInclusion t ∉ W
      rwa [ht]
    · exact Subtype.ext ht

include hW hg in
theorem targetComplement :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
      ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) P.openNeighborhood =
    P.relativeComplement ∪ (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding) ⁻¹'
      (RetractionComparison.Constructions.sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) := by
  rw [globalTargetComplement Z W hW]
  have hi := congrArg (fun S : Set P.neighborhood => Sᶜ) (normalZero_image Z x P W hW g hg)
  have hk : (Subtype.val ⁻¹' (W : Set V.analyticSpace)ᶜ : Set P.neighborhood)ᶜ =
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace) (W : Set V.analyticSpace) P.openNeighborhood := by
    ext y
    exact not_not
  exact ((RetractionZeroLocus.Constructions.equations_support_complement P Z.closed.isEmbedding g).trans (hi.trans hk)).symm

include hW hg in
theorem cylinder_le :
    HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen (X := V.analyticSpace) P.openNeighborhood
      (Immersion.Retraction.Constructions.retractionOpen Z P.openNeighborhood (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding)
        (RetractionComparison.Constructions.sourceEquationOpen Z x P g)) ≤ W := by
  intro y hy
  change y ∈ Subtype.val '' (Immersion.Retraction.Constructions.retractionOpen Z P.openNeighborhood
    (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding)
    (RetractionComparison.Constructions.sourceEquationOpen Z x P g) : Set P.openNeighborhood) at hy
  obtain ⟨w, hw, rfl⟩ := hy
  have hc : w ∈ P.relativeComplement ∪
      (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding) ⁻¹'
        (RetractionComparison.Constructions.sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) := Or.inr hw
  rw [← targetComplement Z x P W hW g hg, globalTargetComplement Z W hW] at hc
  exact hc

end AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions.Support

namespace AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions

/-! The original supported Gysin isomorphism on a normal neighborhood
is the actual source-retraction Thom map, for a closed subset whose
local source equation is prescribed geometrically. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions.Support OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Retraction.Constructions
  RetractionComparison.Constructions Immersion.RetractionComparison.Constructions Immersion.Retraction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)
  (W : Opens V.analyticSpace) (hW : (W : Set V.analyticSpace)ᶜ ⊆ Set.range Z.regularComplementInclusion)
  (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ))
  (hg : ∀ y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding,
    g y = 0 ↔ Z.regularComplementInclusion y.val ∉ W)

include hW in
theorem targetEquality :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
      ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) P.openNeighborhood =
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace) (W : Set V.analyticSpace) P.openNeighborhood :=
  congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace) A P.openNeighborhood)
    (Support.globalTargetComplement Z W hW)

include hW hg in
theorem normalTargetEquality :
    P.relativeComplement ∪ (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding) ⁻¹'
      (RetractionComparison.Constructions.sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) =
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace) (W : Set V.analyticSpace) P.openNeighborhood :=
  (Support.targetComplement Z x P W hW g hg).symm.trans (targetEquality Z x P W hW)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def localGysinIso :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding))
      (RetractionComparison.Constructions.sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) (2 * q) ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace) (W : Set V.analyticSpace) P.openNeighborhood) (2 * (p + q)) :=
  (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding))
    (Support.sourceComplement Z x P W g hg) (2 * q)).symm ≪≫
    Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha W P.openNeighborhood (2 * q) ≪≫
    eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
        ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) P.openNeighborhood) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of P.neighborhood) (targetEquality Z x P W hW) (2 * (p + q))

theorem localGysinIso_eq_retraction :
    localGysinIso Z x P W hW g hg a ha =
    Retraction.Constructions.normalRetractionThomIso Z a ha x P (RetractionComparison.Constructions.sourceEquationOpen Z x P g) (2 * q) ≪≫
      eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
        (P.relativeComplement ∪ (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding) ⁻¹'
          (RetractionComparison.Constructions.sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding))) n)
        (Nat.mul_add 2 p q).symm) ≪≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of P.neighborhood) (normalTargetEquality Z x P W hW g hg) (2 * (p + q)) := by
  have hr := Immersion.RetractionComparison.Constructions.retractionThomIso_eq_original Z a ha P.openNeighborhood
    (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding)
    (HodgeConjecture.DegreeTwo.NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction P Z.closed.isEmbedding)
    (RetractionComparison.Constructions.sourceEquationOpen Z x P g) W (Support.cylinder_le Z x P W hW g hg)
    (Support.sourceComplement Z x P W g hg) (Support.targetComplement Z x P W hW g hg) (2 * q)
  unfold Retraction.Constructions.normalRetractionThomIso
  rw [hr]
  apply Iso.ext
  simp only [localGysinIso, Iso.trans_hom, Iso.symm_hom, AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr,
    eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans]

end AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions

end

end OAI

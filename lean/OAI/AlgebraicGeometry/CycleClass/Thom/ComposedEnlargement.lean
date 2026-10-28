import OAI.AlgebraicGeometry.CycleClass.Thom.Composed
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceNaturality

/-! # Composed Enlargement -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ComposedEnlargement.Constructions

noncomputable section

/-! The genuine Gysin map takes an inner Thom class with enlarged
support to the composite Thom class with the corresponding enlarged
intersection support. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceNaturality.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions
  ComposedSupport.Constructions Composed.Constructions.ThomClass Intersection.Gysin.Constructions ImageIntersectionTo.Constructions.Normal
  Relative.MapDegreeSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q)
  {L : Type} (v : L → V.analyticSpace)
  (hCv : Set.range (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion ⊆ Set.range v)

include hCv

theorem sourceEnlargement_mapsTo : Set.MapsTo (𝟙 Z.regularAnalyticSpace)
    (Z.regularComplementInclusion ⁻¹' (Set.range v)ᶜ) (Set.range C.regularComplementInclusion)ᶜ := by
  intro x hx hC
  obtain ⟨z, hz⟩ := hC
  exact hx (hCv ⟨z, congrArg Z.regularComplementInclusion hz⟩)

theorem targetEnlargement_mapsTo : Set.MapsTo (𝟙 V.analyticSpace)
    (Set.range Z.regularComplementInclusion ∩ Set.range v)ᶜ
    (Set.range (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion)ᶜ := by
  intro x hx hD
  obtain ⟨z, hz⟩ := hD
  exact hx ⟨⟨C.regularComplementInclusion z, hz⟩, hCv ⟨z, hz⟩⟩

variable (hv : IsOpen (Set.range v)ᶜ)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem composedGysin_enlargement :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Z.regularAnalyticSpace)
      (sourceEnlargement_mapsTo Z C v hCv) (2 * q) ≫
      (Intersection.Gysin.Constructions.intersectionGysinIso (q := q) Z a ha v hv).hom =
    (ComposedSupport.Constructions.composedThomGysinIso Z C a ha).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 V.analyticSpace)
        (targetEnlargement_mapsTo Z C v hCv) (2 * (p + q)) := by
  let O : Opens V.analyticSpace := ⟨(Set.range v)ᶜ, hv⟩
  let W := ComposedSupport.Constructions.composedComplement Z C
  have hOW : O ≤ W := fun _ hx hD => hx (hCv hD)
  let s₁ := AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr Z.regularAnalyticSpace (ComposedSupport.Constructions.composedSourceComplement Z C) (2 * q)
  let s₂ := Iso.refl (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Z.regularAnalyticSpace
    (Z.regularComplementInclusion ⁻¹' (Set.range v)ᶜ) (2 * q))
  let t₁ := eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr V.analyticSpace (ComposedSupport.Constructions.composedTargetComplement Z C) (2 * (p + q))
  let t₂ := eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      ((Z.regularThomComplementOpen ⊔ O : Opens V.analyticSpace) : Set V.analyticSpace) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr V.analyticSpace (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq Z.regularComplementInclusion v)
      (2 * (p + q))
  have hs := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality (𝟙 Z.regularAnalyticSpace)
    (rfl : Z.regularComplementInclusion ⁻¹' (O : Set V.analyticSpace) = _)
    (ComposedSupport.Constructions.composedSourceComplement Z C) (fun _ hx => hOW hx) (sourceEnlargement_mapsTo Z C v hCv) (2 * q)
  have ht := Relative.MapDegreeSupport.Constructions.relativePairMap_degreeSupport (𝟙 V.analyticSpace)
    (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq Z.regularComplementInclusion v) (ComposedSupport.Constructions.composedTargetComplement Z C)
    (fun _ hx => (sup_le_sup_left hOW Z.regularThomComplementOpen) hx)
    (targetEnlargement_mapsTo Z C v hCv) (Nat.mul_add 2 p q).symm
  have hn := Immersion.GlobalSourceNaturality.Constructions.Construction.regularSourceThomSupportedGlobalIso_support_naturality Z a ha hOW (2 * q)
  have h := Immersion.SupportedSourceNaturality.Constructions.Construction.sourceTargetIso_naturality s₁ s₂
    (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha W (2 * q))
    (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha O (2 * q)) t₁ t₂ _ _ _ _ hs hn ht
  simpa only [s₁, s₂, t₁, t₂, O, W, Intersection.Gysin.Constructions.intersectionGysinIso, ComposedSupport.Constructions.composedThomGysinIso,
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id, Category.assoc] using h

theorem intersectionGysin_enlarged_innerThom :
    (Intersection.Gysin.Constructions.intersectionGysinIso (q := q) Z a ha v hv).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Z.regularAnalyticSpace)
        (sourceEnlargement_mapsTo Z C v hCv) (2 * q) C.regularThomClass) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 V.analyticSpace)
      (targetEnlargement_mapsTo Z C v hCv) (2 * (p + q)) (Open.ClosedImmersionComposition.Constructions.compose Z C).regularThomClass := by
  have h := ConcreteCategory.congr_hom (composedGysin_enlargement Z C v hCv hv a ha) C.regularThomClass
  simpa only [ConcreteCategory.comp_apply, Composed.Constructions.ThomClass.composedThomGysinIso_innerThom] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ComposedEnlargement.Constructions

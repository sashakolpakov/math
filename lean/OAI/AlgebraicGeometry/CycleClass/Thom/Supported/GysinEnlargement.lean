import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceNaturality

/-! # Gysin Enlargement -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.GysinEnlargement.Constructions

noncomputable section

/-! The original Gysin map with an arbitrary closed support inside
the immersion image commutes with enlargement to intersection support. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceNaturality.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinLocalIso.Constructions.Support OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions
  Intersection.Gysin.Constructions ImageIntersectionTo.Constructions.Normal Relative.MapDegreeSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (W : Opens V.analyticSpace) (hW : (W : Set V.analyticSpace)ᶜ ⊆ Set.range Z.regularComplementInclusion)
  {L : Type} (v : L → V.analyticSpace) (hv : IsOpen (Set.range v)ᶜ)
  (hOW : (Set.range v)ᶜ ⊆ (W : Set V.analyticSpace))

include hOW in
theorem source_mapsTo : Set.MapsTo (𝟙 Z.regularAnalyticSpace)
    (Z.regularComplementInclusion ⁻¹' (Set.range v)ᶜ) (Z.regularComplementInclusion ⁻¹' (W : Set V.analyticSpace)) :=
  fun _ hy => hOW hy

include hW hOW in
theorem target_mapsTo : Set.MapsTo (𝟙 V.analyticSpace)
    (Set.range Z.regularComplementInclusion ∩ Set.range v)ᶜ (W : Set V.analyticSpace) := by
  intro y hy
  by_contra hn
  have hz := hW hn
  have hv' : y ∈ Set.range v := by
    by_contra hvn
    exact hn (hOW hvn)
  exact hy ⟨hz, hv'⟩

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem globalGysinIso_enlargement :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Z.regularAnalyticSpace)
      (source_mapsTo Z W v hOW) (2 * q) ≫ (Intersection.Gysin.Constructions.intersectionGysinIso (q := q) Z a ha v hv).hom =
    (Normal.GysinRestriction.Constructions.globalGysinIso Z W hW a ha q).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 V.analyticSpace)
        (target_mapsTo Z W hW v hOW) (2 * (p + q)) := by
  let O : Opens V.analyticSpace := ⟨(Set.range v)ᶜ, hv⟩
  have hle : O ≤ W := hOW
  let t₂ := eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      ((Z.regularThomComplementOpen ⊔ O : Opens V.analyticSpace) : Set V.analyticSpace) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr V.analyticSpace (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq Z.regularComplementInclusion v) (2 * (p + q))
  have hn := Immersion.GlobalSourceNaturality.Constructions.Construction.regularSourceThomSupportedGlobalIso_support_naturality Z a ha hle (2 * q)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Z.regularAnalyticSpace)
      (source_mapsTo Z W v hOW) (2 * q) ≫ (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha O (2 * q)).hom =
    (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha W (2 * q)).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 V.analyticSpace)
        (A := ((Z.regularThomComplementOpen ⊔ O : Opens V.analyticSpace) : Set V.analyticSpace))
        (B := ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace))
        (fun _ hy => (sup_le_sup_left hle Z.regularThomComplementOpen) hy) (2 * p + 2 * q) at hn
  have ht := Relative.MapDegreeSupport.Constructions.relativePairMap_degreeSupport (𝟙 V.analyticSpace)
    (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq Z.regularComplementInclusion v) (Normal.GysinLocalIso.Constructions.Support.globalTargetComplement Z W hW)
    (fun _ hy => (sup_le_sup_left hle Z.regularThomComplementOpen) hy)
    (target_mapsTo Z W hW v hOW) (Nat.mul_add 2 p q).symm
  have ht' := congrArg (fun f => (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha W (2 * q)).hom ≫ f) ht
  have h := (congrArg (fun f => f ≫ t₂.hom) hn).trans
    (by simpa only [t₂, AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, Iso.trans_hom, Category.assoc] using ht')
  simpa only [t₂, O, Normal.GysinRestriction.Constructions.globalGysinIso, Intersection.Gysin.Constructions.intersectionGysinIso,
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, Iso.trans_hom, Category.assoc] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.GysinEnlargement.Constructions

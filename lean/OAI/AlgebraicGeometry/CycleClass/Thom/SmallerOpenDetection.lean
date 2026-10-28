import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionAmbientTransport
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageEquality
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity

/-! # Smaller Open Detection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.SmallerOpenDetection.Constructions

/-! The actual Thom class on an ambient open restricts to the actual Thom class of any equal-image immersion on a smaller ambient open. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionAmbientTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageEquality.Constructions.ThomInvariant OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (U P : Opens V.analyticSpace) (hP : P ≤ U)
  (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V U) p)

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance : MetrizableSpace P := P.isOpenEmbedding'.isEmbedding.metrizableSpace

def smallerImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V P) p :=
  Closed.ImmersionAmbientTransport.Constructions.transport (Closed.ImmersionOpenRestriction.Constructions.restrict Z (Open.SubsetHomeomorph.Constructions.insideOpen U P)) (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP)
    (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph_analytic (G := V.analyticModel) U P hP)
    (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph_symm_analytic (G := V.analyticModel) U P hP) rfl

theorem smallerOpen_mapsTo : Set.MapsTo (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP)
    (Set.range (smallerImmersion U P hP Z).regularComplementInclusion)ᶜ (Set.range Z.regularComplementInclusion)ᶜ :=
  Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_mapsTo (M := Z.regularAnalyticSpace) (N := U) (N' := P)
    (E := Z.regularAnalyticModel) (G := V.analyticModel)
    Z.regularComplementInclusion Z.holomorphic (Open.SubsetHomeomorph.Constructions.insideOpen U P)
    (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP)

theorem smallerImmersion_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP)
      (smallerOpen_mapsTo U P hP Z) (2 * p) Z.regularThomClass =
        (smallerImmersion U P hP Z).regularThomClass := by
  exact Open.ImageComplement.Constructions.ThomAmbientTransport.ThomClass_open_ambientTransport (M := Z.regularAnalyticSpace) (N := U) (N' := P)
    (E := Z.regularAnalyticModel) (G := V.analyticModel) (H := V.analyticModel)
    Z.regularComplementInclusion Z.holomorphic
    (Open.SubsetHomeomorph.Constructions.insideOpen U P) (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP) Z.differential_injective Z.closed
    ((Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph_analytic (G := V.analyticModel) U P hP).mdifferentiable (by simp))
    ((Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph_symm_analytic (G := V.analyticModel) U P hP).mdifferentiable (by simp))
    (smallerImmersion U P hP Z).holomorphic (smallerImmersion U P hP Z).differential_injective
    p Z.regularComplement_complexImmersionCodimension
    (smallerImmersion U P hP Z).regularComplement_complexImmersionCodimension

variable (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V P) p)
  (hC : Set.range C.regularComplementInclusion = Set.range (smallerImmersion U P hP Z).regularComplementInclusion)

include hC in
theorem equalImage_mapsTo : Set.MapsTo (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP)
    (Set.range C.regularComplementInclusion)ᶜ (Set.range Z.regularComplementInclusion)ᶜ := by
  intro x hx
  apply smallerOpen_mapsTo U P hP Z
  rwa [← hC]

theorem smallerOpen_Thom_of_image :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP)
      (equalImage_mapsTo U P hP Z C hC) (2 * p) Z.regularThomClass = C.regularThomClass := by
  let e := eqToIso (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of P) A (2 * p)) (congrArg Set.compl hC))
  apply e.toLinearEquiv.injective
  have hs := ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP) (congrArg Set.compl hC)
    (equalImage_mapsTo U P hP Z C hC) (smallerOpen_mapsTo U P hP Z) (2 * p) Z.regularThomClass
  have ht := ImageEquality.Constructions.ThomInvariant.regularThomClass_eq_of_image (smallerImmersion U P hP Z) C hC
  exact hs.trans ((smallerImmersion_Thom U P hP Z).trans ht.symm)

end AlgebraicGeometry.CycleClass.Thom.SmallerOpenDetection.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.SmallerOpenDetection.Constructions.Class

/-! Supported classes on an ambient open are detected on smaller opens of the original ambient space, with any genuine equal-image local immersion. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmallerOpenDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (U P : Opens V.analyticSpace) (hP : P ≤ U)
  (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V U) p)

theorem smallerImmersion_range : Set.range (smallerImmersion U P hP Z).regularComplementInclusion =
    (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP) ⁻¹' Set.range Z.regularComplementInclusion := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, rfl⟩
  · rintro ⟨x, hx⟩
    have hxP : Z.regularComplementInclusion x ∈ Open.SubsetHomeomorph.Constructions.insideOpen U P := by
      change (Z.regularComplementInclusion x).val ∈ P
      rw [hx]
      exact y.property
    refine ⟨⟨x, hxP⟩, ?_⟩
    apply Subtype.ext
    change (Z.regularComplementInclusion x).val = y.val
    exact congrArg Subtype.val hx

variable (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V P) p)
  (hC : Set.range C.regularComplementInclusion = Set.range (smallerImmersion U P hP Z).regularComplementInclusion)

include hC in
theorem insideOpen_mapsTo : Set.MapsTo (NormalPair.TransportRestriction.Constructions.ambientTransportMap (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of U) (Set.range Z.regularComplementInclusion)ᶜ (Open.SubsetHomeomorph.Constructions.insideOpen U P))
    (Set.range C.regularComplementInclusion)ᶜ := by
  intro x hx
  rw [hC, smallerImmersion_range]
  exact hx

theorem smallerPullback_factor (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP)
      (equalImage_mapsTo U P hP Z C hC) n ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP))
        (insideOpen_mapsTo U P hP Z C hC) n =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (Set.range Z.regularComplementInclusion)ᶜ (Open.SubsetHomeomorph.Constructions.insideOpen U P) n := by
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (NormalPair.TransportRestriction.Constructions.ambientTransportMap (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP)) (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP)
    (insideOpen_mapsTo U P hP Z C hC) (equalImage_mapsTo U P hP Z C hC) n
  exact h.trans (ThomOpenRestriction.Constructions.pairMap_congr
    (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_factor (Open.SubsetHomeomorph.Constructions.insideOpen U P) (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U P hP))
    ((equalImage_mapsTo U P hP Z C hC).comp (insideOpen_mapsTo U P hP Z C hC)) (fun _ hx => hx) n)

theorem relativeClass_eq_of_smaller_presentations
    (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V U) p)
    (P : Z.regularAnalyticSpace → Opens V.analyticSpace) (hP : ∀ x, P x ≤ U)
    (hx : ∀ x, (Z.regularComplementInclusion x).val ∈ P x)
    (C : ∀ x, Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V (P x)) p)
    (hC : ∀ x, Set.range (C x).regularComplementInclusion =
      Set.range (smallerImmersion U (P x) (hP x) Z).regularComplementInclusion)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (Set.range Z.regularComplementInclusion)ᶜ (2 * p))
    (hab : ∀ x, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.SubsetHomeomorph.Constructions.smallerOpenMap U (P x) (hP x))
      (equalImage_mapsTo U (P x) (hP x) Z (C x) (hC x)) (2 * p) a =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.SubsetHomeomorph.Constructions.smallerOpenMap U (P x) (hP x))
        (equalImage_mapsTo U (P x) (hP x) Z (C x) (hC x)) (2 * p) b) : a = b := by
  apply Immersion.SheafPurity.Constructions.SupportDetection.relativeClass_eq_of_neighborhoods Z (fun x => Open.SubsetHomeomorph.Constructions.insideOpen U (P x)) hx
  intro x
  have ha := ConcreteCategory.congr_hom (smallerPullback_factor U (P x) (hP x) Z (C x) (hC x) (2 * p)) a
  have hb := ConcreteCategory.congr_hom (smallerPullback_factor U (P x) (hP x) Z (C x) (hC x) (2 * p)) b
  exact ha.symm.trans ((congrArg (fun c => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (NormalPair.TransportRestriction.Constructions.ambientTransportMap (Open.SubsetHomeomorph.Constructions.smallerOpenHomeomorph U (P x) (hP x)))
    (insideOpen_mapsTo U (P x) (hP x) Z (C x) (hC x)) (2 * p) c) (hab x)).trans hb)

end AlgebraicGeometry.CycleClass.Thom.SmallerOpenDetection.Constructions.Class

end

end OAI

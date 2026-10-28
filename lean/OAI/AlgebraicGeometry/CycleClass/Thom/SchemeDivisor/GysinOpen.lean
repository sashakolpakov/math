import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinSmall
import OAI.AlgebraicGeometry.CycleClass.Thom.SmallerOpenDetection

/-! # Gysin Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinOpen.Constructions

noncomputable section

/-! On every ambient open where the regular source divisor has its full image, the actual supported Gysin class is the actual Thom class of that image immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinSmall.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmallerOpenDetection.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.SmallerOpenDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  [AlgebraicGeometry.IsNoetherian X.left]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (z : {x : X.left // Order.coheight x = 1})
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  (hR : ((Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageImmersion.Constructions.regularDivisorMap i z))) =
    (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

theorem divisorGysinClass_open_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (OpenImmersion.Constructions.divisorOpenImmersion_mapsTo i z p hp U hR) (2 * (p + 1)) (Gysin.Constructions.divisorGysinClass i z p hp a ha) =
      (OpenImmersion.Constructions.divisorOpenImmersion i z p hp U hR).regularThomClass := by
  classical
  let Z := OpenImmersion.Constructions.divisorOpenImmersion i z p hp U hR
  have hex (x : Z.regularAnalyticSpace) := GysinSmall.Constructions.exists_small_divisorGysin_Thom i z p hp x.val U
    (by
      rw [← ImageImmersion.Constructions.regularDivisorMap_apply i z x.val]
      exact x.property) a ha
  choose P hP hPU hThom using hex
  let C (x : Z.regularAnalyticSpace) := ImageImmersion.Constructions.localDivisorImmersion i z p hp x.val (P x) (hP x)
  have hC (x : Z.regularAnalyticSpace) : Set.range (C x).regularComplementInclusion =
      Set.range (SmallerOpenDetection.Constructions.smallerImmersion (V := Scheme.ClosedImmersion.Constructions.schemeManifold Y) U (P x).openNeighborhood (hPU x) Z).regularComplementInclusion := by
    rw [SmallerOpenDetection.Constructions.Class.smallerImmersion_range]
    change Set.range (ImageImmersion.Constructions.localDivisorImmersion i z p hp x.val (P x) (hP x)).regularComplementInclusion =
      (Open.SubsetHomeomorph.Constructions.smallerOpenMap U (P x).openNeighborhood (hPU x)) ⁻¹'
        Set.range (OpenImmersion.Constructions.divisorOpenImmersion i z p hp U hR).regularComplementInclusion
    rw [ImageImmersion.Constructions.localDivisorImmersion_range, OpenImmersion.Constructions.divisorOpenImmersion_range]
    rfl
  apply SmallerOpenDetection.Constructions.Class.relativeClass_eq_of_smaller_presentations (V := Scheme.ClosedImmersion.Constructions.schemeManifold Y) U Z (fun x => (P x).openNeighborhood) hPU
    (fun x => by
      change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageImmersion.Constructions.regularDivisorMap i z) x.val ∈ (P x).neighborhood
      rw [ImageImmersion.Constructions.regularDivisorMap_apply]
      exact (P x).point_mem_neighborhood) C hC
  intro x
  let jP := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (P x).neighborhood
  have heq := Normal.GysinRestriction.Constructions.ThomClass.supportEquality (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.RegularSupport.Constructions.regularInclusion X (Purity.Constructions.primeSupport X z) x.val) (P x)
    (Gysin.Constructions.divisorImageOpen i z) (C x) (ImageImmersion.Constructions.localDivisorImmersion_range i z p hp x.val (P x) (hP x))
  have hCP : Set.MapsTo jP (Set.range (C x).regularComplementInclusion)ᶜ
      (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := by
    intro y hy
    exact (Set.ext_iff.mp heq y).mpr hy
  have hl : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) jP hCP (2 * (p + 1))
      (Gysin.Constructions.divisorGysinClass i z p hp a ha) = (C x).regularThomClass :=
    (ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast jP heq (fun _ hy => hy) hCP (2 * (p + 1))
      (Gysin.Constructions.divisorGysinClass i z p hp a ha)).symm.trans (hThom x)
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (Open.SubsetHomeomorph.Constructions.smallerOpenMap U (P x).openNeighborhood (hPU x))
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (SmallerOpenDetection.Constructions.equalImage_mapsTo (V := Scheme.ClosedImmersion.Constructions.schemeManifold Y) U (P x).openNeighborhood (hPU x) Z (C x) (hC x))
      (OpenImmersion.Constructions.divisorOpenImmersion_mapsTo i z p hp U hR) (2 * (p + 1))) (Gysin.Constructions.divisorGysinClass i z p hp a ha)
  have h₂ := ConcreteCategory.congr_hom
    (ThomOpenRestriction.Constructions.pairMap_congr (Open.SubsetHomeomorph.Constructions.smallerOpenMap_comp U (P x).openNeighborhood (hPU x))
      ((OpenImmersion.Constructions.divisorOpenImmersion_mapsTo i z p hp U hR).comp
        (SmallerOpenDetection.Constructions.equalImage_mapsTo (V := Scheme.ClosedImmersion.Constructions.schemeManifold Y) U (P x).openNeighborhood (hPU x) Z (C x) (hC x))) hCP (2 * (p + 1)))
    (Gysin.Constructions.divisorGysinClass i z p hp a ha)
  exact (h₁.trans (h₂.trans hl)).trans
    (SmallerOpenDetection.Constructions.smallerOpen_Thom_of_image (V := Scheme.ClosedImmersion.Constructions.schemeManifold Y) U (P x).openNeighborhood (hPU x) Z (C x) (hC x)).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinOpen.Constructions

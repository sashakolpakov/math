import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Equation
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product
import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup

/-! # Image Equality -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ImageEquality.Constructions

/-! The genuine complex Thom class of a closed complex submanifold
depends only on its image, with no choice of source parametrization. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions.Support
  Equation.Constructions.ThomClass NormalPair.Differential.Constructions ExteriorImageCup.Constructions.Restriction
  Normal.Product.Constructions.Class ThomOpenRestriction.Constructions Immersion.IntersectionCoordinates.Constructions
  Immersion.SheafPurity.Constructions.SupportDetection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (h : Set.range D.regularComplementInclusion = Set.range Z.regularComplementInclusion)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)

include h in
theorem localComplement :
    (Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict D P.openNeighborhood).regularComplementInclusion)ᶜ = P.relativeComplement := by
  rw [Closed.ImmersionOpenRestriction.Constructions.Support.restricted_range, h]
  rfl

include h in
theorem localEquation (y : P.neighborhood) :
    y ∈ Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict D P.openNeighborhood).regularComplementInclusion ↔ P.normalCoordinate y = 0 := by
  have hr := Set.ext_iff.mp (Closed.ImmersionOpenRestriction.Constructions.Support.restricted_range D P.openNeighborhood) y
  have hh := Set.ext_iff.mp h y.val
  exact (hr.trans hh).trans (P.mem_range_iff y)

local instance : ChartedSpace V.analyticModel P.neighborhood :=
  inferInstanceAs (ChartedSpace V.analyticModel P.openNeighborhood)

theorem localThom_eq_normal
    (hPd : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)))
    (hPa : ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) ω
      P.ambientChart P.ambientChart.source) :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood) A (2 * p)) (localComplement Z D h x P))
      (Closed.ImmersionOpenRestriction.Constructions.restrict D P.openNeighborhood).regularThomClass = P.rationalClassFin := by
  have ht := Equation.Constructions.ThomClass.equation_pullback_eq_Thom (Closed.ImmersionOpenRestriction.Constructions.restrict D P.openNeighborhood) P.normalCoordinate
    (localEquation Z D h x P) (NormalPair.Differential.Constructions.normalCoordinate_analytic (G := V.analyticModel) P hPa)
    (fun y => NormalPair.Differential.Constructions.normalCoordinate_submersion (G := V.analyticModel) P hPd
      ((Closed.ImmersionOpenRestriction.Constructions.restrict D P.openNeighborhood).regularComplementInclusion y))
  have hc := ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast P.normalCoordinate (localComplement Z D h x P)
    (Equation.Constructions.ThomClass.equation_mapsTo (Closed.ImmersionOpenRestriction.Constructions.restrict D P.openNeighborhood) P.normalCoordinate (localEquation Z D h x P))
    P.normalCoordinate_mapsTo (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  exact (congrArg (fun b => eqToHom (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) A (2 * p))
    (localComplement Z D h x P)) b) ht.symm).trans
      (hc.trans P.rationalClassFin_eq_normalPullback.symm)

end AlgebraicGeometry.CycleClass.Thom.ImageEquality.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.ImageEquality.Constructions.ThomInvariant

/-! Equal actual images of closed complex immersions have identical
canonical supported Thom classes, independently of their source models. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageEquality.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class
  ExteriorImageCup.Constructions.Restriction ThomOpenRestriction.Constructions Open.RestrictionNormalPair.Constructions
  Immersion.IntersectionCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (h : Set.range D.regularComplementInclusion = Set.range Z.regularComplementInclusion)

theorem regularThomClass_eq_of_image :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      V.analyticSpace A (2 * p)) (congrArg Set.compl h)) D.regularThomClass = Z.regularThomClass := by
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique Z.regularComplementInclusion Z.holomorphic
    Z.differential_injective Z.closed p Z.regularComplement_complexImmersionCodimension
    Z.regularFixedNormalPair Z.regularFixedNormalPair_ambientChart_mdifferentiable
  intro x
  let P := Z.regularFixedNormalPair x
  let j := Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace P.neighborhood
  have hj : Set.MapsTo j P.relativeComplement (Set.range D.regularComplementInclusion)ᶜ := by
    intro y hy hd
    exact hy (h ▸ hd)
  have ht := Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast j (congrArg Set.compl h) hj
    (show Set.MapsTo j P.relativeComplement (Set.range Z.regularComplementInclusion)ᶜ from fun _ hy => hy)
    (2 * p) D.regularThomClass
  have hs := ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast j (localComplement Z D h x P)
    (Open.RestrictionNormalPair.Constructions.restriction_mapsTo D P.openNeighborhood) hj (2 * p) D.regularThomClass
  have ho := ThomOpenRestriction.Constructions.regularThomClass_open_restriction D P.openNeighborhood
  have hn := localThom_eq_normal Z D h x P (Z.regularFixedNormalPair_ambientChart_mdifferentiable x)
    (Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff Z x)
  exact ht.trans (hs.symm.trans ((congrArg
    (fun b => eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood) A (2 * p)) (localComplement Z D h x P)) b) ho).trans hn))

end AlgebraicGeometry.CycleClass.Thom.ImageEquality.Constructions.ThomInvariant

end

end OAI

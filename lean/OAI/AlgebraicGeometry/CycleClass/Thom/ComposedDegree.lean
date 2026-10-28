import OAI.AlgebraicGeometry.CycleClass.Thom.ComposedEnlargement
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.GysinDegree

/-! # Composed Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ComposedDegree.Constructions

noncomputable section

/-! Composition of genuine Thom classes in a specified total degree,
including the actual enlargement to an intersection support. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComposedEnlargement.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.GysinDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q) (d : ℕ) (hd : p + q = d)

def composedThomInDegree : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
    (Set.range (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion)ᶜ (2 * d) :=
  Degree.Constructions.ThomClass.complexThomClassInDegree (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion (Open.ClosedImmersionComposition.Constructions.compose Z C).holomorphic
    (Open.ClosedImmersionComposition.Constructions.compose Z C).differential_injective (Open.ClosedImmersionComposition.Constructions.compose Z C).closed d
    ((Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplement_complexImmersionCodimension.trans hd)

theorem composedThomInDegree_cast :
    eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion)ᶜ (2 * n)) hd) (Open.ClosedImmersionComposition.Constructions.compose Z C).regularThomClass =
      composedThomInDegree Z C d hd := by
  cases hd
  rfl

variable {L : Type} (v : L → V.analyticSpace)
  (hCv : Set.range (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion ⊆ Set.range v)
  (hv : IsOpen (Set.range v)ᶜ)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Set.range Z.regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem gysinAt_enlarged_innerThom :
    (Intersection.GysinDegree.Constructions.intersectionGysinAt Z a ha v hv d hd).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Z.regularAnalyticSpace)
        (ComposedEnlargement.Constructions.sourceEnlargement_mapsTo Z C v hCv) (2 * q) C.regularThomClass) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 V.analyticSpace)
      (ComposedEnlargement.Constructions.targetEnlargement_mapsTo Z C v hCv) (2 * d) (composedThomInDegree Z C d hd) := by
  cases hd
  exact ComposedEnlargement.Constructions.intersectionGysin_enlarged_innerThom Z C v hCv hv a ha

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ComposedDegree.Constructions

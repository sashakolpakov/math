import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion

/-! # Open Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions

noncomputable section

/-! The actual regular divisor image is a closed immersion on any ambient open where it equals the full divisor image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.ImageImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (z : {x : X.left // Order.coheight x = 1})
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  (hR : ((Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ImageImmersion.Constructions.regularDivisorMap i z))) =
    (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ)

def divisorOpenImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (Scheme.ClosedImmersion.Constructions.schemeManifold Y) U) (p + 1) :=
  Scheme.OpenImmersion.Constructions.restrictedImmersion (ImageImmersion.Constructions.regularDivisorMap i z) U (p + 1) (ImageImmersion.Constructions.imageCodimension z p hp) (by
    rw [hR]
    exact (Gysin.Constructions.divisorImageOpen i z).isOpen.isClosed_compl.preimage continuous_subtype_val)

theorem divisorOpenImmersion_range : Set.range (divisorOpenImmersion i z p hp U hR).regularComplementInclusion =
    (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⁻¹' (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ :=
  (Scheme.OpenImmersion.Constructions.restrictedMap_range (ImageImmersion.Constructions.regularDivisorMap i z) U).trans hR

theorem divisorOpenImmersion_mapsTo : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
    (Set.range (divisorOpenImmersion i z p hp U hR).regularComplementInclusion)ᶜ
    (Gysin.Constructions.divisorImageOpen i z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := by
  intro x hx
  rw [divisorOpenImmersion_range] at hx
  exact Classical.not_not.mp hx

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions

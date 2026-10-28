import OAI.Analysis.HodgeTheory.Decomposition.ComponentLaplacian
import OAI.Analysis.HodgeTheory.Decomposition.ComponentRotation

/-! # Component Harmonic Types -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonicTypes.Constructions

noncomputable section

/-! Actual harmonic component families decompose into harmonic pure forms. -/

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  [∀ C : irreducibleComponents X.carrier, MeasurableSpace (X.componentVariety C).analyticSpace]
  [∀ C : irreducibleComponents X.carrier, BorelSpace (X.componentVariety C).analyticSpace] (n : ℕ)

theorem componentPositiveLaplacian_projection (i : Core.Constructions.Bidegree (n + 1)) (a : X.componentForms (n + 1)) :
    ComponentLaplacian.Constructions.componentPositiveLaplacian X n (Projectors.Constructions.componentProjection X (n + 1) i a) =
      Projectors.Constructions.componentProjection X (n + 1) i (ComponentLaplacian.Constructions.componentPositiveLaplacian X n a) :=
  (ComponentRotation.Constructions.componentOperator_projection X (n + 1) (ComponentLaplacian.Constructions.componentPositiveLaplacian X n)
    (ComponentLaplacian.Constructions.componentPositiveLaplacian_pure X n) i a).symm

theorem componentProjection_harmonic (i : Core.Constructions.Bidegree (n + 1)) (a : X.componentForms (n + 1))
    (ha : ComponentLaplacian.Constructions.componentPositiveLaplacian X n a = 0) :
    ComponentLaplacian.Constructions.componentPositiveLaplacian X n (Projectors.Constructions.componentProjection X (n + 1) i a) = 0 := by
  rw [componentPositiveLaplacian_projection, ha, map_zero]

abbrev ComponentHarmonics := (ComponentLaplacian.Constructions.componentPositiveLaplacian X n).ker

def componentHarmonicType (i : Core.Constructions.Bidegree (n + 1)) : Submodule ℂ (ComponentHarmonics X n) :=
  (Core.Constructions.pureFormsAt X (n + 1) i).comap (ComponentHarmonics X n).subtype

def componentHarmonicProjection (i : Core.Constructions.Bidegree (n + 1)) : Module.End ℂ (ComponentHarmonics X n) :=
  ((Projectors.Constructions.componentProjection X (n + 1) i).comp (ComponentHarmonics X n).subtype).codRestrict
    (ComponentHarmonics X n) (fun a => componentProjection_harmonic X n i a.val a.property)

theorem componentHarmonicProjection_pure (i : Core.Constructions.Bidegree (n + 1)) (a : ComponentHarmonics X n) :
    componentHarmonicProjection X n i a ∈ componentHarmonicType X n i :=
  Projectors.Constructions.componentProjection_pure X (n + 1) i a.val

theorem sum_componentHarmonicProjection (a : ComponentHarmonics X n) :
    (∑ i : Core.Constructions.Bidegree (n + 1), componentHarmonicProjection X n i a) = a := by
  apply Subtype.ext
  change (ComponentHarmonics X n).subtype (∑ i : Core.Constructions.Bidegree (n + 1), componentHarmonicProjection X n i a) = a.val
  rw [map_sum]
  exact Projectors.Constructions.sum_componentProjection X (n + 1) a.val

end

end OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonicTypes.Constructions

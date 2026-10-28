import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusRealManifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntrinsicPeriodComparison
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Torus Operations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusOperations.CM.Abelian.Algebraization.AlgebraicTorusOperations

noncomputable section

/-! # CMAbelianVariety: actual algebraic addition and inversion on the projective period model -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Manifold
open OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates

variable (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

local instance tensor_integral : IsIntegral (X ⊗ X).left := Albanese.Construction.Smooth.smooth_tensor_integral X X
local instance tensor_smooth : Smooth (X ⊗ X).hom := by dsimp; infer_instance

def addition (e : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e (e.symm (p ≫ fst X X) + e.symm (p ≫ snd X X))

def inversion (e : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e (-e.symm p)

theorem addition_holomorphic (e : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) e)
    (hi : MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, Φ.space)) e.symm) :
    MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model (X ⊗ X))) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (addition Φ X e) := by
  have hfst := (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (fst X X) 1).mdifferentiable one_ne_zero
  have hsnd := (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (snd X X) 1).mdifferentiable one_ne_zero
  have hadd : MDifferentiable ((𝓘(ℂ, Φ.space)).prod (𝓘(ℂ, Φ.space)))
      (𝓘(ℂ, Φ.space)) (fun p : Φ.periodTorus × Φ.periodTorus => p.1 + p.2) :=
    (contMDiff_add (𝓘(ℂ, Φ.space)) 1).mdifferentiable one_ne_zero
  exact he.comp (hadd.comp ((hi.comp hfst).prodMk (hi.comp hsnd)))

theorem inversion_holomorphic (e : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) e)
    (hi : MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, Φ.space)) e.symm) :
    MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (inversion Φ X e) := by
  have hneg : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, Φ.space))
      (fun p : Φ.periodTorus => -p) :=
    (contMDiff_neg (I := 𝓘(ℂ, Φ.space)) (n := 1)).mdifferentiable one_ne_zero
  exact he.comp (hneg.comp hi)

theorem exists_operations (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom)
    (e : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) e)
    (hi : MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, Φ.space)) e.symm) :
    ∃ (μ : X ⊗ X ⟶ X) (ν : X ⟶ X),
      (∀ p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X), p ≫ μ = addition Φ X e p) ∧
      ∀ p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, p ≫ ν = inversion Φ X e p := by
  let : IsProper X.hom := P.isProper
  let : IsProper (X ⊗ X).hom := by dsimp; infer_instance
  let : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := P.compactSpace_complexPoints
  let : Nonempty (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ⟨e 0⟩
  let PP := Albanese.Construction.SegreClosed.tensorProjectivePresentation X X P P
  let : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) := PP.compactSpace_complexPoints
  let : Nonempty (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) := ⟨lift (e 0) (e 0)⟩
  obtain ⟨μ, hμ⟩ := OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization.exists_algebraic_map PP P (addition Φ X e)
    (addition_holomorphic Φ X e he hi)
  obtain ⟨ν, hν⟩ := OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization.exists_algebraic_map P P (inversion Φ X e)
    (inversion_holomorphic Φ X e he hi)
  exact ⟨μ, ν, hμ, hν⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusOperations.CM.Abelian.Algebraization.AlgebraicTorusOperations

import OAI.RepresentationTheory.Theta.Geometric.Torus.RealManifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph
import OAI.RepresentationTheory.Theta.Geometric.Torus.IntrinsicPeriodComparison
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Algebraic Operations -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.AlgebraicOperations.CM.Algebraization.AlgebraicTorusOperations

noncomputable section

/-! # GeometricTheta: actual algebraic addition and inversion on the projective period model -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Manifold
open OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates

variable (Φ : Data.CM.ProjectivePeriodData) (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

local instance tensor_integral : IsIntegral (X ⊗ X).left := AlgebraicGeometry.Albanese.Construction.Smooth.smooth_tensor_integral X X
local instance tensor_smooth : Smooth (X ⊗ X).hom := by dsimp; infer_instance

def addition (e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e (e.symm (p ≫ fst X X) + e.symm (p ≫ snd X X))

def inversion (e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e (-e.symm p)

theorem addition_holomorphic (e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) e)
    (hi : MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, Φ.space)) e.symm) :
    MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model (X ⊗ X))) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (addition Φ X e) := by
  have hfst := (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (fst X X) 1).mdifferentiable one_ne_zero
  have hsnd := (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (snd X X) 1).mdifferentiable one_ne_zero
  have hadd : MDifferentiable ((𝓘(ℂ, Φ.space)).prod (𝓘(ℂ, Φ.space)))
      (𝓘(ℂ, Φ.space)) (fun p : Φ.periodTorus × Φ.periodTorus => p.1 + p.2) :=
    (contMDiff_add (𝓘(ℂ, Φ.space)) 1).mdifferentiable one_ne_zero
  exact he.comp (hadd.comp ((hi.comp hfst).prodMk (hi.comp hsnd)))

theorem inversion_holomorphic (e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) e)
    (hi : MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, Φ.space)) e.symm) :
    MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (inversion Φ X e) := by
  have hneg : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, Φ.space))
      (fun p : Φ.periodTorus => -p) :=
    (contMDiff_neg (I := 𝓘(ℂ, Φ.space)) (n := 1)).mdifferentiable one_ne_zero
  exact he.comp (hneg.comp hi)

theorem exists_operations (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom)
    (e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) e)
    (hi : MDifferentiable (𝓘(ℂ, OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, Φ.space)) e.symm) :
    ∃ (μ : X ⊗ X ⟶ X) (ν : X ⟶ X),
      (∀ p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X), p ≫ μ = addition Φ X e p) ∧
      ∀ p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, p ≫ ν = inversion Φ X e p := by
  let : IsProper X.hom := P.isProper
  let : IsProper (X ⊗ X).hom := by dsimp; infer_instance
  let : CompactSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := P.compactSpace_complexPoints
  let : Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ⟨e 0⟩
  let PP := AlgebraicGeometry.Albanese.Construction.SegreClosed.tensorProjectivePresentation X X P P
  let : CompactSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) := PP.compactSpace_complexPoints
  let : Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X)) := ⟨lift (e 0) (e 0)⟩
  obtain ⟨μ, hμ⟩ := OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization.exists_algebraic_map PP P (addition Φ X e)
    (addition_holomorphic Φ X e he hi)
  obtain ⟨ν, hν⟩ := OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization.exists_algebraic_map P P (inversion Φ X e)
    (inversion_holomorphic Φ X e he hi)
  exact ⟨μ, ν, hμ, hν⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.AlgebraicOperations.CM.Algebraization.AlgebraicTorusOperations

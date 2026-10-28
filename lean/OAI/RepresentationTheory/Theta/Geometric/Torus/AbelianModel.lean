import OAI.RepresentationTheory.Theta.Geometric.Torus.SmoothProjectiveModel
import OAI.RepresentationTheory.Theta.Geometric.Torus.IntrinsicPeriodComparison
import OAI.RepresentationTheory.Theta.Geometric.Torus.RealManifold
import OAI.RepresentationTheory.Theta.Geometric.Torus.AlgebraicOperations
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GroupFrom
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold

/-! # Abelian Model -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.AbelianModel.CM.Algebraization.AbelianTorusModel

noncomputable section

/-! # GeometricTheta: an actual abelian variety with the prescribed complex period torus -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

local instance abelian_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance abelian_smooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem exists_abelian_model_with_group (Φ : Data.CM.ProjectivePeriodData) :
    ∃ (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space),
      𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ)⟯
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver), ∀ u v, e (u + v) = e u * e v := by
  obtain ⟨n, f, e, hf, hd, hint, hsm, _, he⟩ :=
    SmoothProjectiveModel.CM.Algebraization.SmoothProjectiveTorusModel.exists_smooth_integral_projective_model Φ
  let V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨SmoothProjectiveModel.CM.Algebraization.SmoothProjectiveTorusModel.presentation (range f) hsm, hint⟩
  let X := V.toOver
  let : IsIntegral X.left := hint
  let : Smooth X.hom := hsm
  let : IsProper X.hom := V.presentation.projective.isProper
  let eX : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e
  let j : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion (range f)))
  have hhol := IntrinsicPeriodComparison.CM.Algebraization.biholomorphic Φ X f hf.continuous hd j eX he
  obtain ⟨mulMap, invMap, hmulMap, hinvMap⟩ := AlgebraicOperations.CM.Algebraization.AlgebraicTorusOperations.exists_operations Φ X V.presentation.projective eX hhol.1 hhol.2
  let g : GrpObj X := Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints.group X eX.toEquiv mulMap hmulMap invMap hinvMap
  have hcomm : letI := g; IsCommMonObj X := Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints.commutative X eX.toEquiv mulMap hmulMap invMap hinvMap
  let A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := { variety := V, group := g, commutative := hcomm }
  refine ⟨A, Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.diffeomorph eX hhol.1 hhol.2, ?_⟩
  intro u v
  change eX (u + v) = CategoryTheory.CartesianMonoidalCategory.lift (eX u) (eX v) ≫ mulMap
  rw [hmulMap]
  simp only [AlgebraicOperations.CM.Algebraization.AlgebraicTorusOperations.addition,
    CategoryTheory.CartesianMonoidalCategory.lift_fst,
    CategoryTheory.CartesianMonoidalCategory.lift_snd, eX.symm_apply_apply]

theorem exists_abelian_model (Φ : Data.CM.ProjectivePeriodData) :
    ∃ A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety, Nonempty (Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space),
      𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := by
  obtain ⟨A, e, _⟩ := exists_abelian_model_with_group Φ
  exact ⟨A, ⟨e⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.AbelianModel.CM.Algebraization.AbelianTorusModel

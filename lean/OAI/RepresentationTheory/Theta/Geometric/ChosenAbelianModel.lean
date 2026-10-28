import OAI.RepresentationTheory.Theta.Geometric.ChosenProjective
import OAI.RepresentationTheory.Theta.Geometric.Torus.AbelianModel

/-! # Chosen Abelian Model -/

namespace OAI.RepresentationTheory.Theta.Geometric.ChosenAbelianModel.CM.Torus.Algebraization.ChosenProjectiveModel

noncomputable section

/-! The abelian model retains a prescribed projective period embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem abelian_model {n : ℕ} (Φ : Torus.Data.CM.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) :
    ∃ (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space),
      𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ)⟯
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
      (j : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)),
      IsClosedImmersion j.left ∧ (∀ u v, e (u + v) = e u * e v) ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f t) := by
  obtain ⟨e, hint, hsm, _, he⟩ := ChosenProjective.CM.Torus.Algebraization.ChosenProjectiveModel.smooth_integral_model Φ f hf hd
  let V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨Torus.SmoothProjectiveModel.CM.Algebraization.SmoothProjectiveTorusModel.presentation (range f) hsm, hint⟩
  let X := V.toOver
  let : IsIntegral X.left := hint
  let : Smooth X.hom := hsm
  let : IsProper X.hom := V.presentation.projective.isProper
  let eX : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e
  let j : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion (range f)))
  have hhol := Torus.IntrinsicPeriodComparison.CM.Algebraization.biholomorphic Φ X f hf.continuous hd j eX he
  obtain ⟨mulMap, invMap, hmulMap, hinvMap⟩ := Torus.AlgebraicOperations.CM.Algebraization.AlgebraicTorusOperations.exists_operations Φ X V.presentation.projective eX hhol.1 hhol.2
  let g : GrpObj X := Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints.group X eX.toEquiv mulMap hmulMap invMap hinvMap
  have hcomm : letI := g; IsCommMonObj X := Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints.commutative X eX.toEquiv mulMap hmulMap invMap hinvMap
  let A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := { variety := V, group := g, commutative := hcomm }
  refine ⟨A, Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.diffeomorph eX hhol.1 hhol.2, j, inferInstance, ?_, he⟩
  intro u v
  change eX (u + v) = CategoryTheory.CartesianMonoidalCategory.lift (eX u) (eX v) ≫ mulMap
  rw [hmulMap]
  simp only [Torus.AlgebraicOperations.CM.Algebraization.AlgebraicTorusOperations.addition,
    CategoryTheory.CartesianMonoidalCategory.lift_fst,
    CategoryTheory.CartesianMonoidalCategory.lift_snd, eX.symm_apply_apply]

end

end OAI.RepresentationTheory.Theta.Geometric.ChosenAbelianModel.CM.Torus.Algebraization.ChosenProjectiveModel

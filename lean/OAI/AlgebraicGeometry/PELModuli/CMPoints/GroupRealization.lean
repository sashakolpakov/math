import OAI.Geometry.ComplexTorus.RiemannProjectivity.AbelianModel
import OAI.Geometry.ComplexTorus.RiemannProjectivity.IntrinsicComparison

/-! # Group Realization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupRealization

noncomputable section

/-! Retain the group comparison from the checked RiemannProjectivity construction.
The canonical CM integer lattice can then carry its actual integral
coefficient action through to the algebraic model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.Geometry.ComplexTorus.RiemannProjectivity.IntrinsicComparison.Constructions
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem exists_CM_abelian_model_with_group (hRiemannProjectivity : Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput)
    (Φ : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E),
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ)⟯
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver),
      ∀ u v, e (u + v) = e u * e v := by
  obtain ⟨n, f, e, hf, hd, hint, hsm, _, he⟩ :=
    Geometry.ComplexTorus.RiemannProjectivity.SmoothProjectiveModel.Constructions.SmoothProjectiveTorusModel.exists_smooth_integral_projective_model hRiemannProjectivity Φ
  let V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨Geometry.ComplexTorus.RiemannProjectivity.SmoothProjectiveModel.Constructions.SmoothProjectiveTorusModel.presentation (range f) hsm, hint⟩
  let X := V.toOver
  let : IsIntegral X.left := hint
  let : Smooth X.hom := hsm
  let : IsProper X.hom := V.presentation.projective.isProper
  let eX : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e
  let j : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion (range f)))
  have hhol := Geometry.ComplexTorus.RiemannProjectivity.IntrinsicPeriodComparison.Constructions.biholomorphic Φ X f hf.continuous hd j eX he
  obtain ⟨mulMap, invMap, hmulMap, hinvMap⟩ :=
    Geometry.ComplexTorus.RiemannProjectivity.AlgebraicOperations.Constructions.AlgebraicTorusOperations.exists_operations Φ X V.presentation.projective eX hhol.1 hhol.2
  let g : GrpObj X := Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints.group X eX.toEquiv mulMap hmulMap invMap hinvMap
  have hcomm : letI := g; IsCommMonObj X :=
    Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints.commutative X eX.toEquiv mulMap hmulMap invMap hinvMap
  let A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := { variety := V, group := g, commutative := hcomm }
  refine ⟨A, Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.diffeomorph eX hhol.1 hhol.2, ?_⟩
  intro u v
  change eX (u + v) = CategoryTheory.CartesianMonoidalCategory.lift (eX u) (eX v) ≫ mulMap
  rw [hmulMap]
  simp only [Geometry.ComplexTorus.RiemannProjectivity.AlgebraicOperations.Constructions.AlgebraicTorusOperations.addition,
    CategoryTheory.CartesianMonoidalCategory.lift_fst,
    CategoryTheory.CartesianMonoidalCategory.lift_snd, eX.symm_apply_apply]

theorem exists_CM_group_realization (hRiemannProjectivity : Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput)
    (Φ : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization Φ.hodgeStructure)
      (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E),
        𝓘(ℂ, R.abelianVariety.variety.analyticModel)⟯ R.abelianVariety.variety.analyticSpace),
      ∀ u v, e (u + v) = e u * e v := by
  obtain ⟨A, e, he⟩ := exists_CM_abelian_model_with_group hRiemannProjectivity Φ
  let R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization Φ.hodgeStructure := {
    abelianVariety := A
    comparison := Geometry.ComplexTorus.RiemannProjectivity.IntrinsicComparison.Constructions.rationalComparison Φ A.variety e
    holomorphic := Geometry.ComplexTorus.RiemannProjectivity.IntrinsicComparison.Constructions.holomorphic Φ A e
    antiholomorphic := Geometry.ComplexTorus.RiemannProjectivity.IntrinsicComparison.Constructions.antiholomorphic Φ A e }
  exact ⟨R, e, he⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupRealization

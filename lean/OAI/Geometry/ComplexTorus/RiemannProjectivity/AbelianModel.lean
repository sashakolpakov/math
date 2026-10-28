import OAI.Geometry.ComplexTorus.RiemannProjectivity.AlgebraicOperations
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GroupFrom
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold

/-! # Abelian Model -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.AbelianModel.Constructions.AbelianTorusModel

noncomputable section

/-! # RiemannProjectivity: an actual abelian variety with the prescribed complex period torus -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped _root_.Manifold ContDiff
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

local instance abelian_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance abelian_smooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem exists_abelian_model (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety, Nonempty (Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E),
      𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := by
  obtain ⟨n, f, e, hf, hd, hint, hsm, _, he⟩ :=
    SmoothProjectiveModel.Constructions.SmoothProjectiveTorusModel.exists_smooth_integral_projective_model hRiemannProjectivity Φ
  let V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨SmoothProjectiveModel.Constructions.SmoothProjectiveTorusModel.presentation (range f) hsm, hint⟩
  let X := V.toOver
  let : IsIntegral X.left := hint
  let : Smooth X.hom := hsm
  let : IsProper X.hom := V.presentation.projective.isProper
  let eX : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e
  let j : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion (range f)))
  have hhol := IntrinsicPeriodComparison.Constructions.biholomorphic Φ X f hf.continuous hd j eX he
  obtain ⟨μ, ν, hμ, hν⟩ := AlgebraicOperations.Constructions.AlgebraicTorusOperations.exists_operations Φ X V.presentation.projective eX hhol.1 hhol.2
  let g : GrpObj X := GroupFrom.Constructions.GroupFromPoints.group X eX.toEquiv μ hμ ν hν
  have hcomm : letI := g; IsCommMonObj X := GroupFrom.Constructions.GroupFromPoints.commutative X eX.toEquiv μ hμ ν hν
  let A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := { variety := V, group := g, commutative := hcomm }
  exact ⟨A, ⟨HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.diffeomorph eX hhol.1 hhol.2⟩⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.AbelianModel.Constructions.AbelianTorusModel

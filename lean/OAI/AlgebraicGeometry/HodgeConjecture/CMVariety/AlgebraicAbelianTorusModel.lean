import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.SmoothModel
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntrinsicPeriodComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusRealManifold
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusOperations
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GroupFrom
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold

/-! # Algebraic Abelian Torus Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicAbelianTorusModel.CM.Algebraization.AbelianTorusModel

noncomputable section

/-! # CMAbelianVariety: an actual abelian variety with the prescribed complex period torus -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped _root_.Manifold ContDiff
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

local instance abelian_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance abelian_smooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem exists_abelian_model (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety, Nonempty (Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space),
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ)⟯ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := by
  obtain ⟨n, f, e, hf, hd, hint, hsm, _, he⟩ :=
    SmoothModel.CM.Abelian.Algebraization.SmoothProjectiveTorusModel.exists_smooth_integral_projective_model Φ
  let V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨SmoothModel.CM.Abelian.Algebraization.SmoothProjectiveTorusModel.presentation (range f) hsm, hint⟩
  let X := V.toOver
  let : IsIntegral X.left := hint
  let : Smooth X.hom := hsm
  let : IsProper X.hom := V.presentation.projective.isProper
  let eX : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := e
  let j : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion (range f)))
  have hhol := IntrinsicPeriodComparison.CM.Abelian.Algebraization.biholomorphic Φ X f hf.continuous hd j eX he
  obtain ⟨μ, ν, hμ, hν⟩ := TorusOperations.CM.Abelian.Algebraization.AlgebraicTorusOperations.exists_operations Φ X V.presentation.projective eX hhol.1 hhol.2
  let g : GrpObj X := Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints.group X eX.toEquiv μ hμ ν hν
  have hcomm : letI := g; IsCommMonObj X := Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints.commutative X eX.toEquiv μ hμ ν hν
  let A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := { variety := V, group := g, commutative := hcomm }
  exact ⟨A, ⟨Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.diffeomorph eX hhol.1 hhol.2⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicAbelianTorusModel.CM.Algebraization.AbelianTorusModel

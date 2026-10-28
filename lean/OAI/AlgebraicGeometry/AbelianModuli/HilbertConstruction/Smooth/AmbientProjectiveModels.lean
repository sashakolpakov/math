import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveAmbientModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AmbientClosedModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModelAmbientFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraRecoverySpec
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveClosedModel

/-! # Ambient Projective Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

noncomputable section

/-! A smooth ambient functor model gives a smooth projective scheme in an actual finite coefficient base change of the original ambient gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {R : Type u} [CommRing R] {C : Subalgebra ℤ R}
variable {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J] [Finite J]
variable {G : J ⥤ Over (Spec (.of C))} [∀ i, IsAffine (G.obj i).left]
variable [∀ i, LocallyOfFiniteType (G.obj i).hom]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable (M : AmbientFunctorModel.SmoothAmbientFunctorModel C G)

local instance AmbientFunctorModel.SmoothAmbientFunctorModel.smoothAmbientProjective_original_open {i j : J} (h : i ⟶ j) :
    IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

theorem AmbientFunctorModel.SmoothAmbientFunctorModel.exists_smooth_projective_model
    (P : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (DiagramGluing.smoothDiagramGluedMap G))) :
    ∃ N : Closed.AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R)
      (Affine.CoordinateFunctor.affineCoordinateFunctor M.coefficients M.ambient)
      (Affine.CoordinateFunctor.affineCoordinateFunctor M.coefficients M.source),
      ∃ D : Subalgebra N.closingCoefficients R, D.FG ∧
        Nonempty (ProjectiveClosedModel.SmoothProjectiveClosedModel (T := Spec (.of R))
          (N.ambientBaseChange D
            ((Over.pullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion M.above).toRingHom))).obj
              (Over.mk (DiagramGluing.smoothDiagramGluedMap G)))) (SubalgebraRecoverySpec.subalgebraRecoverySpec (C := N.closingCoefficients) (R := R) D)) := by
  have : Algebra.FiniteType ℤ M.coefficients := M.finiteType
  have : IsNoetherianRing M.coefficients := Algebra.FiniteType.isNoetherianRing ℤ M.coefficients
  let c := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion M.above).toRingHom)
  have {i j : J} (h : i ⟶ j) : IsOpenImmersion (M.ambient.map h).left :=
    Affine.FunctorBaseChange.affineFunctorBaseChange_open G c h
  have : ((M.ambient ⋙ Over.forget (Spec (.of M.coefficients))) ⋙ Scheme.forget).IsLocallyDirected :=
    DiagramPullbackProjection.diagramPullback_locallyDirected G c
  have (i : Jᵒᵖ) : Algebra.Smooth M.coefficients ((Affine.CoordinateFunctor.affineCoordinateFunctor M.coefficients M.source).obj i) :=
    AffineSchemeModels.affineOverAlgebra_smooth M.coefficients (M.source.obj i.unop)
  obtain ⟨N, _⟩ := M.exists_closed_model (⊥ : Subalgebra M.coefficients R) Subalgebra.fg_bot
  obtain ⟨D, _, hD, Y, hs, hn, hp, j, hj, hr⟩ := N.exists_smooth_projective_ambient_model M.ambient
    (Projective.DiagramBaseChange.projectiveDiagramBaseChange G c P) (⊥ : Subalgebra N.closingCoefficients R) Subalgebra.fg_bot
  let e := N.ambientBaseChangeIso D (DiagramPullbackGluedIso.diagramPullbackGluedOverIso G c)
  let r := SubalgebraRecoverySpec.subalgebraRecoverySpec (C := N.closingCoefficients) (R := R) D
  let L : ProjectiveClosedModel.SmoothProjectiveClosedModel
      (N.ambientBaseChange D (Over.mk (DiagramGluing.smoothDiagramGluedMap M.ambient))) r := {
    scheme := Y
    smooth := hs
    noetherian := hn
    projective := hp.some
    embedding := j
    closed := hj
    recovered := hr }
  exact ⟨N, D, hD, ⟨L.transport e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

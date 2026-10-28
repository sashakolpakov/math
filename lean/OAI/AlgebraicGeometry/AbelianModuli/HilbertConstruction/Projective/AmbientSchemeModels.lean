import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AmbientProjectiveModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIntersectionSmoothness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionProjectivity

/-! # Ambient Scheme Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.AmbientSchemeModels

noncomputable section

/-! A projective coefficient scheme whose recovery is smooth has a smooth projective closed model after finite coefficient extensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_smooth_projective_ambient_scheme_model
    {R : Type u} [CommRing R] (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C]
    (X : Over (Spec (.of C))) [CompactSpace X.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom C.val.toRingHom))).obj X).hom]
    (P : ProjectivePresentations.ProjectivePresentation X) :
    ∃ M : HilbertConstruction.Smooth.AmbientFunctorModel.SmoothAmbientFunctorModel C (ReferenceIntersectionFunctor.originalIntersectionFunctor X),
      ∃ N : Closed.AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R)
        (Affine.CoordinateFunctor.affineCoordinateFunctor M.coefficients M.ambient)
        (Affine.CoordinateFunctor.affineCoordinateFunctor M.coefficients M.source),
        ∃ D : Subalgebra N.closingCoefficients R, D.FG ∧
          Nonempty (HilbertConstruction.Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel (T := Spec (.of R))
            (N.ambientBaseChange D
              ((Over.pullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion M.above).toRingHom))).obj X))
            (SubalgebraRecoverySpec.subalgebraRecoverySpec (C := N.closingCoefficients) (R := R) D)) := by
  let G := ReferenceIntersectionFunctor.originalIntersectionFunctor X
  have (i : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) : IsAffine (G.obj i).left := Finite.AffineIntersections.finiteIntersectionChart_affine X i
  have (i : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) : LocallyOfFiniteType (G.obj i).hom :=
    RecoveredIntersectionSmoothness.originalIntersection_finiteType X i
  have (i : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) : Smooth
      ((G ⋙ Over.pullback (Spec.map (CommRingCat.ofHom C.val.toRingHom))).obj i).hom :=
    RecoveredIntersectionSmoothness.originalIntersection_baseChanged_smooth X _ i
  obtain ⟨M⟩ := HilbertConstruction.Smooth.AmbientFunctorModel.exists_smoothAmbientFunctorModel C G
  obtain ⟨N, D, hD, ⟨L⟩⟩ :=
    M.exists_smooth_projective_model (ReferenceIntersectionProjectivity.originalIntersectionGluedProjective X P)
  let c := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion M.above).toRingHom)
  let e := N.ambientBaseChangeIso D ((Over.pullback c).mapIso (ReferenceIntersectionProjectivity.originalIntersectionGluedOverIso X))
  exact ⟨M, N, D, hD, ⟨L.transport e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.AmbientSchemeModels

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedIntersectionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.LocallyDirected

/-! # Recovered Glued Model Existence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The finite intersection model gives a smooth noetherian global model with actual Cartesian recovery. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : FiniteIntersection.IntersectionModel.FiniteIntersectionModel X)

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.exists_recovered_glued_model (E : Subalgebra M.coefficients R) (hE : E.FG) :
    ∃ D : Subalgebra M.coefficients R, E ≤ D ∧ D.FG ∧
      ∃ Y : Over (Spec (.of D)), Smooth Y.hom ∧ IsNoetherian Y.left ∧
        ∃ q : X.left ⟶ Y.left, IsPullback q X.hom Y.hom
          (Spec.map (CommRingCat.ofHom D.val.toRingHom)) := by
  obtain ⟨D, hED, hD, hd⟩ := M.exists_locallyDirected_extension E hE
  have : (M.baseChangedSchemeFunctor D ⋙ Scheme.forget).IsLocallyDirected := hd
  have (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) : IsAffine ((M.baseChangedFunctor D).obj S).left :=
    M.baseChangedFunctor_affine D S
  have (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) : Smooth ((M.baseChangedFunctor D).obj S).hom :=
    M.baseChangedFunctor_smooth D S
  have : Algebra.FiniteType M.coefficients D := (Subalgebra.fg_iff_finiteType D).mp hD
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing M.coefficients D
  let Y : Over (Spec (.of D)) := Over.mk (HilbertConstruction.Smooth.DiagramGluing.smoothDiagramGluedMap (C := D) (M.baseChangedFunctor D))
  exact ⟨D, hED, hD, Y, HilbertConstruction.Smooth.DiagramGluing.smoothDiagramGluedMap_smooth (M.baseChangedFunctor D),
    HilbertConstruction.Smooth.DiagramGluing.smoothDiagramGlued_noetherian (M.baseChangedFunctor D),
    M.recoveredIntersectionMap D, M.recoveredIntersectionMap_isPullback D⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

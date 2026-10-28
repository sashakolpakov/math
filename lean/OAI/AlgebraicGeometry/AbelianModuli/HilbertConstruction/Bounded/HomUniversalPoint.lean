import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFiberFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismIsomorphisms

/-! # Hom Universal Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomUniversalPoint

noncomputable section

/-! Evaluating the native universal bounded monoid homomorphism recovers the represented point; this also identifies its isomorphism locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom] [MonObj A] [MonObj B]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem boundedFamilyMonoidHomUniversal_point {T : Over S}
    (c : T ⟶ MonoidHomParameters.boundedFamilyMonoidHomParameter j P) :
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (MonoidHomRepresentation.boundedFamilyMonoidHomUniversal j P).val.val =
      (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T c).val.val := by
  have h := HomFiberFaithfulness.boundedFamilyMonoidHomPoint_natural j P c (𝟙 _)
  simp only [Category.comp_id] at h
  exact (congrArg (fun D : MonoidHomParameters.BoundedFamilyMonoidHom j P T => D.val.val) h).symm

theorem boundedFamilyMonoidHomUniversal_pullback_isIso_iff {T : Over S}
    (c : T ⟶ MonoidHomParameters.boundedFamilyMonoidHomParameter j P) :
    IsIso ((Over.pullback c.left).map (MonoidHomRepresentation.boundedFamilyMonoidHomUniversal j P).val.val) ↔
      IsIso (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T c).val.val :=
  (Geometric.MorphismIsomorphisms.geometricFamilyMorphismBaseChange_isIso_iff c _).symm.trans
    (iff_of_eq (congrArg IsIso (boundedFamilyMonoidHomUniversal_point j P c)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomUniversalPoint

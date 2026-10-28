import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentedGroupGraphBounds

/-! # Bound Presentation Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Transport graph bounds between specified presentations without rebuilding their records. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X Y : Over S}
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
variable [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]

theorem FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofPresentationsIso
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y)
    (e : X ≅ Y) (hd : P.dimension = Q.dimension)
    (he : HEq (e.hom ≫ Q.embedding) P.embedding)
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (Pm Pi : Polynomial ℚ)
    (hb : D.ProjectiveGraphBounds P Pm Pi) :
    (D.ofIso e).ProjectiveGraphBounds Q Pm Pi := by
  rcases P with ⟨n, i, hi⟩
  rcases Q with ⟨m, j, hj⟩
  dsimp only at hd he hb ⊢
  cases hd
  let : IsClosedImmersion i.left := hi
  let : IsClosedImmersion j.left := hj
  exact FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofIso i j e (eq_of_heq he) D Pm Pi hb

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeLocalPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FieldPullbackEquality

/-! # Graph Local Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphLocalPolynomial

noncomputable section

/-! A morphism from a smooth projective family over any local ring has one actual embedded graph Hilbert polynomial. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

theorem smoothGraph_exists_localHilbertPolynomial
    {R : Type u} [CommRing R] [IsLocalRing R] {A B : Over (Spec (.of R))} {n : ℕ}
    [Smooth A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n) [IsClosedImmersion j.left]
    (f : A ⟶ B) : ∃ P : Polynomial ℚ, Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P f := by
  let F := (MorphismGraphFamilies.morphismGraphFamily f).reembed j
  let e : A ≅ F.scheme := MorphismGraphFamilies.morphismGraphFamilyIso f ≪≫ (MorphismGraphFamilies.morphismGraphFamily f).reembedIso j
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have hS : Smooth (e.inv.left ≫ A.hom) := inferInstance
  have : Smooth F.scheme.hom := (congrArg Smooth e.inv.w).mp hS
  exact F.smooth_exists_localFieldHilbertPolynomial

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphLocalPolynomial

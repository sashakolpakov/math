import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Embedded Graph Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphFamilies

noncomputable section

/-! Graphs in any closed projective product embedding are faithful ideal families and retain the smoothness of their source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem embeddedMorphismGraphFamily_injective {S : Scheme.{u}} {A B : Over S} {n : ℕ}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] :
    Function.Injective (fun p : A ⟶ B => (MorphismGraphFamilies.morphismGraphFamily p).reembed j) :=
  (Closed.Families.FlatClosedFamily.reembed_injective j).comp MorphismGraphFamilies.morphismGraphFamily_injective

theorem embeddedMorphismGraphFamily_smooth {S : Scheme.{u}} {A B : Over S} {n : ℕ}
    [Smooth A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (p : A ⟶ B) :
    Smooth ((MorphismGraphFamilies.morphismGraphFamily p).reembed j).scheme.hom := by
  let e := MorphismGraphFamilies.morphismGraphFamilyIso p ≪≫ (MorphismGraphFamilies.morphismGraphFamily p).reembedIso j
  have : IsIso e.inv.left := (Over.forget S).map_isIso e.inv
  have h : Smooth (e.inv.left ≫ A.hom) := inferInstance
  exact (congrArg Smooth e.inv.w).mp h

theorem embeddedGraphHilbertFamily_smooth {S : Scheme.{u}} {A B : Over S} {n : ℕ}
    [Smooth A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)
    (p : {p : A ⟶ B // Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p}) :
    Smooth (Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily j P p).family.scheme.hom :=
  embeddedMorphismGraphFamily_smooth j p.val

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.EmbeddedGraphFamilies

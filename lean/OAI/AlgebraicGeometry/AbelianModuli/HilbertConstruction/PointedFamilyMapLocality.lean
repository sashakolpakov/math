import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismCompositionLaws
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedHomomorphism

/-! # Pointed Family Map Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedFamilyMapLocality

noncomputable section

/-! Identity preservation is local for every subcanonical topology. On arbitrary tests of fixed projective Noetherian abelian families, locally pointed maps therefore preserve the full group law. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem geometricFamilyMap_preserves_unit_of_cover
    {S : Scheme.{u}} (A B : Over S) [MonObj A] [MonObj B]
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (T : Over S) (R : Sieve T) (hR : R ∈ (J.over S) T)
    (f : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)
    (h : ∀ {U : Over S} (c : U ⟶ T), R c →
      η[(Over.pullback U.hom).obj A] ≫ Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f =
        η[(Over.pullback U.hom).obj B]) :
    η[(Over.pullback T.hom).obj A] ≫ f = η[(Over.pullback T.hom).obj B] := by
  let F := Over.pullback T.hom
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp
    (Family.MorphismSheaf.geometricFamilyMorphismFunctor_isSheaf_subcanonical (𝟙_ (Over S)) B J) R hR).isSeparatedFor
  have he : F.map η[A] ≫ f = F.map η[B] := by
    apply hsep.ext
    intro U c hc
    change Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (F.map η[A] ≫ f) =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (F.map η[B])
    rw [Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_map_comp, Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_original,
      Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_original]
    let G := Over.pullback U.hom
    have hu := h c hc
    change (Functor.LaxMonoidal.ε G ≫ G.map η[A]) ≫ Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f =
      Functor.LaxMonoidal.ε G ≫ G.map η[B] at hu
    exact (cancel_epi (Functor.LaxMonoidal.ε G)).mp
      ((Category.assoc (Functor.LaxMonoidal.ε G) (G.map η[A])
        (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f)).symm.trans hu)
  change (Functor.LaxMonoidal.ε F ≫ F.map η[A]) ≫ f = Functor.LaxMonoidal.ε F ≫ F.map η[B]
  rw [Category.assoc, he]

theorem relativeFamilyMap_isMonHom_of_locally_pointed
    {S : Scheme.{u}} [IsNoetherian S] {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (T : Over S) (R : Sieve T) (hR : R ∈ (J.over S) T)
    (f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme)
    (h : ∀ {U : Over S} (c : U ⟶ T), R c →
      η[(A.pullback U.hom).scheme] ≫ Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f = η[(B.pullback U.hom).scheme]) :
    IsMonHom f :=
  Relative.UniversalPointedHomomorphism.relativeUniversalPointedMap_isMonHom A B PA PB T f
    (geometricFamilyMap_preserves_unit_of_cover A.scheme B.scheme J T R hR f h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedFamilyMapLocality

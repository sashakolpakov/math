import OAI.CategoryTheory.Isomorphisms.IsoConjugateMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyKernelRecovery

/-! # Graph Isomorphism Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-! Isomorphic source and target families with compatible projective
embeddings have exactly the same ideal-defined graph families after
transporting the morphism. All relative Hilbert conditions are preserved. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {S : Scheme.{u}} {X X' Y Y' : Over S}
variable (e : X ≅ X') (d : Y ≅ Y') (p : X ⟶ Y)

theorem GraphIsomorphismTransport.familyGraph_transport :
    MorphismGraphFamilies.familyGraph p ≫ (e.hom ⊗ₘ d.hom) =
      e.hom ≫ MorphismGraphFamilies.familyGraph (e.inv ≫ p ≫ d.hom) := by
  apply CartesianMonoidalCategory.hom_ext
  · have hf : MorphismGraphFamilies.familyGraph p ≫ fst X Y = 𝟙 X := lift_fst _ _
    have hf' : MorphismGraphFamilies.familyGraph (e.inv ≫ p ≫ d.hom) ≫ fst X' Y' = 𝟙 X' := lift_fst _ _
    calc
      _ = MorphismGraphFamilies.familyGraph p ≫ fst X Y ≫ e.hom := by rw [Category.assoc, tensorHom_fst]
      _ = e.hom := by rw [← Category.assoc, hf, Category.id_comp]
      _ = _ := by rw [Category.assoc, hf', Category.comp_id]
  · have hs : MorphismGraphFamilies.familyGraph p ≫ snd X Y = p := lift_snd _ _
    have hs' : MorphismGraphFamilies.familyGraph (e.inv ≫ p ≫ d.hom) ≫ snd X' Y' = e.inv ≫ p ≫ d.hom := lift_snd _ _
    calc
      _ = MorphismGraphFamilies.familyGraph p ≫ snd X Y ≫ d.hom := by rw [Category.assoc, tensorHom_snd]
      _ = p ≫ d.hom := by rw [← Category.assoc, hs]
      _ = _ := by rw [Category.assoc, hs', Iso.hom_inv_id_assoc]

variable [Flat X.hom] [LocallyOfFinitePresentation X.hom]
variable [Flat X'.hom] [LocallyOfFinitePresentation X'.hom]
variable [IsSeparated Y.hom] [IsSeparated Y'.hom]
variable {n : ℕ} (j : X ⊗ Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j' : X' ⊗ Y' ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
variable [IsClosedImmersion j.left] [IsClosedImmersion j'.left]
variable (h : (e.hom ⊗ₘ d.hom) ≫ j' = j)

include h

theorem GraphIsomorphismTransport.embeddedGraphFamily_transport :
    (MorphismGraphFamilies.morphismGraphFamily p).reembed j =
      (MorphismGraphFamilies.morphismGraphFamily (e.inv ≫ p ≫ d.hom)).reembed j' := by
  let a := MorphismGraphFamilies.familyGraph p ≫ j
  let b := MorphismGraphFamilies.familyGraph (e.inv ≫ p ≫ d.hom) ≫ j'
  let : IsClosedImmersion a.left := by
    change IsClosedImmersion ((MorphismGraphFamilies.familyGraph p).left ≫ j.left)
    infer_instance
  let : IsClosedImmersion b.left := by
    change IsClosedImmersion ((MorphismGraphFamilies.familyGraph (e.inv ≫ p ≫ d.hom)).left ≫ j'.left)
    infer_instance
  let : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have hab : e.hom ≫ b = a := by
    change e.hom ≫ (MorphismGraphFamilies.familyGraph (e.inv ≫ p ≫ d.hom) ≫ j') = MorphismGraphFamilies.familyGraph p ≫ j
    rw [← Category.assoc, ← GraphIsomorphismTransport.familyGraph_transport, Category.assoc, h]
  have hk : a.left.ker = b.left.ker :=
    (congrArg Scheme.Hom.ker (congrArg Over.Hom.left hab)).symm.trans
      (Scheme.Hom.ker_comp_of_isIso e.hom.left b.left)
  have hf : Closed.Families.FlatClosedFamily.ofEmbedding a = Closed.Families.FlatClosedFamily.ofEmbedding b := by
    apply Closed.Families.FlatClosedFamily.ext
    exact hk
  exact (Closed.Families.FlatClosedFamily.ofEmbedding_reembed (MorphismGraphFamilies.familyGraph p) j).trans
    (hf.trans (Closed.Families.FlatClosedFamily.ofEmbedding_reembed (MorphismGraphFamilies.familyGraph (e.inv ≫ p ≫ d.hom)) j').symm)

theorem GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.transport_iff (P : Polynomial ℚ) :
    GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p ↔
      GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j' P (CategoryTheory.Isomorphisms.IsoConjugateMap.isoConjugateMap e d p) := by
  have hf := GraphIsomorphismTransport.embeddedGraphFamily_transport e d p j j' h
  exact (congrArg (fun F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n) =>
    ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ S),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback x).homogeneousIdeal.toIdeal P) hf).to_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

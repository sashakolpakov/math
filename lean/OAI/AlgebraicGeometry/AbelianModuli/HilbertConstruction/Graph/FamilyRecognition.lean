import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismGraphFamilies

/-! # Family Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A closed family is the graph of a morphism exactly when its first projection is an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {A B : Over S}

theorem Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion {P Z : Over S} (i : Z ⟶ P)
    [IsClosedImmersion i.left] [Flat Z.hom] [LocallyOfFinitePresentation Z.hom] :
    (Closed.Families.FlatClosedFamily.ofEmbeddingIso i).hom ≫ (Closed.Families.FlatClosedFamily.ofEmbedding i).inclusion = i := by
  apply Over.OverMorphism.ext
  exact i.left.toImage_imageι

def Closed.Families.FlatClosedFamily.graphMorphism (F : Closed.Families.FlatClosedFamily (A ⊗ B))
    [IsIso (F.inclusion ≫ fst A B)] : A ⟶ B :=
  inv (F.inclusion ≫ fst A B) ≫ F.inclusion ≫ snd A B

theorem Closed.Families.FlatClosedFamily.graphMorphism_graph (F : Closed.Families.FlatClosedFamily (A ⊗ B))
    [IsIso (F.inclusion ≫ fst A B)] :
    MorphismGraphFamilies.familyGraph F.graphMorphism = inv (F.inclusion ≫ fst A B) ≫ F.inclusion := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MorphismGraphFamilies.familyGraph, lift_fst, Category.assoc, IsIso.inv_hom_id]
  · simp only [MorphismGraphFamilies.familyGraph, lift_snd, Closed.Families.FlatClosedFamily.graphMorphism, Category.assoc]

instance Graph.FamilyRecognition.morphismGraphFamily_firstProjection_isIso (p : A ⟶ B)
    [IsSeparated B.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom] :
    IsIso ((MorphismGraphFamilies.morphismGraphFamily p).inclusion ≫ fst A B) := by
  have h : (MorphismGraphFamilies.morphismGraphFamilyIso p).hom ≫ (MorphismGraphFamilies.morphismGraphFamily p).inclusion ≫ fst A B = 𝟙 A := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ fst A B) (Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion (MorphismGraphFamilies.familyGraph p))).trans
        (lift_fst (𝟙 A) p))
  have hi : IsIso ((MorphismGraphFamilies.morphismGraphFamilyIso p).hom ≫
      (MorphismGraphFamilies.morphismGraphFamily p).inclusion ≫ fst A B) := h.symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

theorem Closed.Families.FlatClosedFamily.graphMorphism_family (F : Closed.Families.FlatClosedFamily (A ⊗ B))
    [IsIso (F.inclusion ≫ fst A B)] [IsSeparated B.hom] [Flat A.hom]
    [LocallyOfFinitePresentation A.hom] : MorphismGraphFamilies.morphismGraphFamily F.graphMorphism = F := by
  apply Closed.Families.FlatClosedFamily.ext
  have h := congrArg Over.Hom.left F.graphMorphism_graph
  have : IsIso (inv (F.inclusion ≫ fst A B)).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (inv (F.inclusion ≫ fst A B))))
  change (MorphismGraphFamilies.familyGraph F.graphMorphism).left.ker = F.ideal
  rw [h]
  change ((inv (F.inclusion ≫ fst A B)).left ≫ F.inclusion.left).ker = F.ideal
  exact (Scheme.Hom.ker_comp_of_isIso _ _).trans F.ideal.ker_subschemeι

def Graph.FamilyRecognition.morphismGraphFamilyEquiv [IsSeparated B.hom] [Flat A.hom]
    [LocallyOfFinitePresentation A.hom] :
    (A ⟶ B) ≃ {F : Closed.Families.FlatClosedFamily (A ⊗ B) // IsIso (F.inclusion ≫ fst A B)} where
  toFun p := ⟨MorphismGraphFamilies.morphismGraphFamily p, inferInstance⟩
  invFun F := by
    letI := F.property
    exact F.val.graphMorphism
  left_inv p := by
    apply MorphismGraphFamilies.morphismGraphFamily_injective
    exact (MorphismGraphFamilies.morphismGraphFamily p).graphMorphism_family
  right_inv F := by
    let := F.property
    apply Subtype.ext
    exact F.val.graphMorphism_family

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

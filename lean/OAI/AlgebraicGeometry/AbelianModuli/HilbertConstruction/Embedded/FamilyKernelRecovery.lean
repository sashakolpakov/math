import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Reembedding

/-! # Family Kernel Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An isomorphism preserving an actual closed embedding recovers its ideal-defined family, and reembedding an embedding family composes the embeddings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

local instance Embedded.FamilyKernelRecovery.embeddedFamilyCompositeClosed {S : Scheme.{u}} {X P Q : Over S}
    (i : X ⟶ P) [IsClosedImmersion i.left] (j : P ⟶ Q) [IsClosedImmersion j.left] :
    IsClosedImmersion (i ≫ j).left := inferInstanceAs (IsClosedImmersion (i.left ≫ j.left))

theorem Closed.Families.FlatClosedFamily.ofEmbedding_eq_of_iso
    {S : Scheme.{u}} {X P : Over S} [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    (i : X ⟶ P) [IsClosedImmersion i.left] (F : Closed.Families.FlatClosedFamily P)
    (e : X ≅ F.scheme) (he : e.hom ≫ F.inclusion = i) : Closed.Families.FlatClosedFamily.ofEmbedding i = F := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  apply Closed.Families.FlatClosedFamily.ext
  change i.left.ker = F.ideal
  have h : e.hom.left ≫ F.inclusion.left = i.left := congrArg Over.Hom.left he
  rw [← h]
  exact (Scheme.Hom.ker_comp_of_isIso _ _).trans F.ideal.ker_subschemeι

theorem Closed.Families.FlatClosedFamily.ofEmbedding_reembed
    {S : Scheme.{u}} {X P Q : Over S} [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    (i : X ⟶ P) [IsClosedImmersion i.left] (j : P ⟶ Q) [IsClosedImmersion j.left] :
    (Closed.Families.FlatClosedFamily.ofEmbedding i).reembed j = Closed.Families.FlatClosedFamily.ofEmbedding (i ≫ j) := by
  have : Flat (Closed.Families.FlatClosedFamily.ofEmbedding i).scheme.hom := (Closed.Families.FlatClosedFamily.ofEmbedding i).flat
  have : LocallyOfFinitePresentation (Closed.Families.FlatClosedFamily.ofEmbedding i).scheme.hom :=
    (Closed.Families.FlatClosedFamily.ofEmbedding i).locallyFinitePresentation
  have : IsClosedImmersion (i ≫ j).left := inferInstanceAs (IsClosedImmersion (i.left ≫ j.left))
  symm
  apply Closed.Families.FlatClosedFamily.ofEmbedding_eq_of_iso (i ≫ j)
    ((Closed.Families.FlatClosedFamily.ofEmbedding i).reembed j)
    (Closed.Families.FlatClosedFamily.ofEmbeddingIso i ≪≫ (Closed.Families.FlatClosedFamily.ofEmbedding i).reembedIso j)
  change (Closed.Families.FlatClosedFamily.ofEmbeddingIso i).hom ≫
      (Closed.Families.FlatClosedFamily.ofEmbeddingIso ((Closed.Families.FlatClosedFamily.ofEmbedding i).inclusion ≫ j)).hom ≫
        (Closed.Families.FlatClosedFamily.ofEmbedding ((Closed.Families.FlatClosedFamily.ofEmbedding i).inclusion ≫ j)).inclusion = i ≫ j
  rw [Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion, ← Category.assoc,
    Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

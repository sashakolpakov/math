import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingKernelIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport

/-! # Reembedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Reembed actual closed families through a closed ambient immersion without losing their identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P Q : Over S} (j : P ⟶ Q) [IsClosedImmersion j.left]

instance Closed.Families.FlatClosedFamily.inclusion_comp_closed (F : Closed.Families.FlatClosedFamily P) :
    IsClosedImmersion (F.inclusion ≫ j).left :=
  IsClosedImmersion.comp F.inclusion.left j.left

def Closed.Families.FlatClosedFamily.reembed (F : Closed.Families.FlatClosedFamily P) : Closed.Families.FlatClosedFamily Q := by
  letI : Flat F.scheme.hom := F.flat
  letI : LocallyOfFinitePresentation F.scheme.hom := F.locallyFinitePresentation
  exact Closed.Families.FlatClosedFamily.ofEmbedding (F.inclusion ≫ j)

def Closed.Families.FlatClosedFamily.reembedIso (F : Closed.Families.FlatClosedFamily P) : F.scheme ≅ (F.reembed j).scheme := by
  letI : Flat F.scheme.hom := F.flat
  letI : LocallyOfFinitePresentation F.scheme.hom := F.locallyFinitePresentation
  exact Closed.Families.FlatClosedFamily.ofEmbeddingIso (F.inclusion ≫ j)

theorem Closed.Families.FlatClosedFamily.reembed_ideal (F : Closed.Families.FlatClosedFamily P) :
    (F.reembed j).ideal = (F.inclusion.left ≫ j.left).ker := rfl

theorem Closed.Families.FlatClosedFamily.reembed_injective :
    Function.Injective (fun F : Closed.Families.FlatClosedFamily P => F.reembed j) := by
  intro F G h
  have hk : (F.inclusion ≫ j).left.ker = (G.inclusion ≫ j).left.ker :=
    congrArg Closed.Families.FlatClosedFamily.ideal h
  let e : F.scheme ≅ G.scheme := Closed.EmbeddingKernelIso.closedEmbeddingKernelIso (F.inclusion ≫ j) (G.inclusion ≫ j) hk
  have : Mono j := Over.mono_of_mono_left j
  have he : e.hom ≫ G.inclusion = F.inclusion := by
    apply (cancel_mono j).mp
    exact (Category.assoc _ _ _).trans
      (Closed.EmbeddingKernelIso.closedEmbeddingKernelIso_embedding (F.inclusion ≫ j) (G.inclusion ≫ j) hk)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  apply Closed.Families.FlatClosedFamily.ext
  have hc : e.hom.left ≫ G.ideal.subschemeι = F.ideal.subschemeι := congrArg Over.Hom.left he
  exact F.ideal.ker_subschemeι.symm.trans
    ((congrArg Scheme.Hom.ker hc.symm).trans
      ((Scheme.Hom.ker_comp_of_isIso e.hom.left G.ideal.subschemeι).trans G.ideal.ker_subschemeι))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

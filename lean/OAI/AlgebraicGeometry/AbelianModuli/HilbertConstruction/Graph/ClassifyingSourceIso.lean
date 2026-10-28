import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.PullbackRecoveryIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyKernelRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyBaseChange

/-! # Classifying Source Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! When an actual pulled-back projective family is an embedded morphism graph, its source is canonically isomorphic to the categorical family pullback, compatibly with the embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance Graph.ClassifyingSourceIso.graphClassifierCompositeClosed {S : Scheme.{u}} {X Y Z : Over S}
    (i : X ⟶ Y) [IsClosedImmersion i.left] (j : Y ⟶ Z) [IsClosedImmersion j.left] :
    IsClosedImmersion (i ≫ j).left := inferInstanceAs (IsClosedImmersion (i.left ≫ j.left))

variable {R T : Scheme.{u}} {A B : Over T} {n : ℕ}
variable [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
variable (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver R n)) (c : T ⟶ R)

def Closed.Families.FlatClosedFamily.projectiveBaseChangeIso : (F.projectiveBaseChange c).scheme ≅ (Over.pullback c).obj F.scheme :=
  F.pullbackAlongIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c n) c (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback c n)

theorem Closed.Families.FlatClosedFamily.projectiveBaseChangeIso_inclusion :
    (F.projectiveBaseChangeIso c).hom ≫ (Over.pullback c).map F.inclusion =
      (F.projectiveBaseChange c).inclusion ≫
        (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c n) c (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback c n)).hom :=
  F.pullbackAlongIso_inclusion (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c n) c (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback c n)

variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T n) [IsClosedImmersion j.left] (p : A ⟶ B)
variable (he : F.projectiveBaseChange c = (MorphismGraphFamilies.morphismGraphFamily p).reembed j)

include he

theorem Graph.ClassifyingSourceIso.graphClassifyingSourceKernel :
    (MorphismGraphFamilies.familyGraph p ≫ j).left.ker = (F.projectiveBaseChange c).inclusion.left.ker := by
  have h : Closed.Families.FlatClosedFamily.ofEmbedding (MorphismGraphFamilies.familyGraph p ≫ j) = F.projectiveBaseChange c :=
    (Closed.Families.FlatClosedFamily.ofEmbedding_reembed (MorphismGraphFamilies.familyGraph p) j).symm.trans he.symm
  have hk := congrArg Closed.Families.FlatClosedFamily.ideal h
  exact hk.trans (F.projectiveBaseChange c).ideal.ker_subschemeι.symm

def Graph.ClassifyingSourceIso.graphClassifyingSourceIso : A ≅ (Over.pullback c).obj F.scheme :=
  Closed.EmbeddingKernelIso.closedEmbeddingKernelIso (MorphismGraphFamilies.familyGraph p ≫ j) (F.projectiveBaseChange c).inclusion
    (Graph.ClassifyingSourceIso.graphClassifyingSourceKernel F c j p he) ≪≫
      F.projectiveBaseChangeIso c

theorem Graph.ClassifyingSourceIso.graphClassifyingSourceIso_embedding :
    (Graph.ClassifyingSourceIso.graphClassifyingSourceIso F c j p he).hom ≫ (Over.pullback c).map F.inclusion =
      (MorphismGraphFamilies.familyGraph p ≫ j) ≫
        (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c n) c (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback c n)).hom := by
  unfold Graph.ClassifyingSourceIso.graphClassifyingSourceIso
  rw [Iso.trans_hom, Category.assoc, F.projectiveBaseChangeIso_inclusion, ← Category.assoc,
    Closed.EmbeddingKernelIso.closedEmbeddingKernelIso_embedding]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

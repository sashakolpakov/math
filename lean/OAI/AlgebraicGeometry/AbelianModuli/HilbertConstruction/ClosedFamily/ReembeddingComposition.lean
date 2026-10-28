import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyKernelRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyBaseChange

/-! # Reembedding Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Reembedding ideal-defined closed families composes exactly, and their categorical pullback agrees with the family of the pulled-back inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

local instance ClosedFamily.ReembeddingComposition.closedFamilyCompositeClosed {S : Scheme.{u}} {P Q R : Over S}
    (j : P ⟶ Q) [IsClosedImmersion j.left] (k : Q ⟶ R) [IsClosedImmersion k.left] :
    IsClosedImmersion (j ≫ k).left := inferInstanceAs (IsClosedImmersion (j.left ≫ k.left))

local instance ClosedFamily.ReembeddingComposition.closedFamilyPulledInclusionClosed {S T : Scheme.{u}} (f : T ⟶ S)
    {P : Over S} (F : Closed.Families.FlatClosedFamily P) : IsClosedImmersion ((Over.pullback f).map F.inclusion).left :=
  MorphismProperty.overPullbackMap f F.inclusion (inferInstance : IsClosedImmersion F.inclusion.left)

local instance ClosedFamily.ReembeddingComposition.closedFamilyPulledSourceFlat {S T : Scheme.{u}} (f : T ⟶ S)
    {P : Over S} (F : Closed.Families.FlatClosedFamily P) : Flat ((Over.pullback f).obj F.scheme).hom := by
  have : Flat F.scheme.hom := F.flat
  exact inferInstanceAs (Flat (Limits.pullback.snd F.scheme.hom f))

local instance ClosedFamily.ReembeddingComposition.closedFamilyPulledSourceFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S)
    {P : Over S} (F : Closed.Families.FlatClosedFamily P) :
    LocallyOfFinitePresentation ((Over.pullback f).obj F.scheme).hom := by
  have : LocallyOfFinitePresentation F.scheme.hom := F.locallyFinitePresentation
  exact inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd F.scheme.hom f))

theorem Closed.Families.FlatClosedFamily.reembed_comp {S : Scheme.{u}} {P Q R : Over S}
    (F : Closed.Families.FlatClosedFamily P) (j : P ⟶ Q) [IsClosedImmersion j.left]
    (k : Q ⟶ R) [IsClosedImmersion k.left] :
    (F.reembed j).reembed k = F.reembed (j ≫ k) := by
  have : Flat F.scheme.hom := F.flat
  have : LocallyOfFinitePresentation F.scheme.hom := F.locallyFinitePresentation
  change (Closed.Families.FlatClosedFamily.ofEmbedding (F.inclusion ≫ j)).reembed k = _
  rw [Closed.Families.FlatClosedFamily.ofEmbedding_reembed]
  apply Closed.Families.FlatClosedFamily.ext
  change ((F.inclusion ≫ j) ≫ k).left.ker = (F.inclusion ≫ (j ≫ k)).left.ker
  rw [Category.assoc]

theorem Closed.Families.FlatClosedFamily.baseChange_eq_ofEmbedding_pullbackInclusion
    {S T : Scheme.{u}} {P : Over S} (F : Closed.Families.FlatClosedFamily P) (f : T ⟶ S) :
    F.baseChange f = Closed.Families.FlatClosedFamily.ofEmbedding ((Over.pullback f).map F.inclusion) := by
  apply Closed.Families.FlatClosedFamily.ext
  change F.ideal.comap (Limits.pullback.fst P.hom f) = ((Over.pullback f).map F.inclusion).left.ker
  have hk := Graph.FamilyBaseChange.closedImmersion_ker_baseChange (Graph.FamilyBaseChange.overPullback_map_isPullback_flip f F.inclusion)
  exact (hk.trans (congrArg (fun I => I.comap (Limits.pullback.fst P.hom f)) F.ideal.ker_subschemeι)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

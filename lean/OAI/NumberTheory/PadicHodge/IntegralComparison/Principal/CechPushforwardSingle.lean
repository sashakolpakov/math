import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoordinates

/-! # Cech Pushforward Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardSingle

noncomputable section

/-! The full original pushforward comparison has the literal
unshifted coefficient comparison in its original single coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem paste {C : Type*} [Category C] {L A B D E F : C}
    (a : L ⟶ A) (b : L ⟶ B) (u : A ⟶ B) (lo : L ≅ D)
    (ag : A ⟶ E) (bg : B ⟶ F) (r : E ⟶ F) (cc : D ⟶ E) (dd : D ⟶ F)
    (hp : a ≫ u = b) (ha : a ≫ ag = lo.hom ≫ cc)
    (hb : b ≫ bg = lo.hom ≫ dd) (hu : u ≫ bg = ag ≫ r) :
    cc ≫ r = dd := by
  apply (cancel_epi lo.hom).mp
  rw [← Category.assoc, ← ha, Category.assoc, ← hu, ← Category.assoc, hp, hb]

universe u v
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {C : Type u} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  (P : (Opens Y)ᵒᵖ ⥤ D) (c g : ℕ)
attribute [local instance] RelativeCech.ReindexData.preimage_limits
  CechPushforwardCoordinates.pulled_products

abbrev singleComplex := (single ((Opens Y)ᵒᵖ ⥤ D) (.up ℕ) c).obj P
abbrev restriction := OrderedCech.ReindexTotal.restriction (RelativeCech.ReindexData.preimage f) (A := D)

variable
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (RelativeCech.ReindexTotal.pushed f (singleComplex P c)) (g+c))]
  [IsIso (RelativeCech.Refinement.homology ((RelativeCech.ReindexData.preimage f).obj (F.obj (⊤_ C)))
    ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J) (RelativeCech.Reindex.mapped f B J s) (singleComplex P c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (RelativeCech.ReindexTotal.pushed f (singleComplex P c))) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap ((RelativeCech.ReindexData.preimage f).obj ∘ V)
    ((RelativeCech.ReindexData.preimage f).obj ∘ T) (RelativeCech.ReindexGlobal.rightRefinement f V T t) (singleComplex P c)) (g+c))]

local instance pulled_relative :
    IsIso (RelativeCech.Refinement.homology
      ((CechPushforwardCoordinates.pulled f F).obj (⊤_ C))
      ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J) (RelativeCech.Reindex.mapped f B J s) (singleComplex P c) (g+c)) :=
  (inferInstance : IsIso (RelativeCech.Refinement.homology ((RelativeCech.ReindexData.preimage f).obj (F.obj (⊤_ C)))
    ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J) (RelativeCech.Reindex.mapped f B J s) (singleComplex P c) (g+c)))

theorem comparison :
    MappedSingleCoordinates.coefficientComparison (restriction f) P c g
      F W B J r s V T l t ≫ homologyMap (OrderedCech.Reindex.iso (RelativeCech.ReindexData.preimage f) V P).hom g =
    PresheafSingleCoordinates.coefficientComparison P c g
      (CechPushforwardCoordinates.pulled f F) W
      ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J)
      (RelativeCech.Reindex.mapped f (F.obj ∘ W) J r) (RelativeCech.Reindex.mapped f B J s)
      ((RelativeCech.ReindexData.preimage f).obj ∘ V) ((RelativeCech.ReindexData.preimage f).obj ∘ T)
      (RelativeCech.ReindexGlobal.leftRefinement f (F.obj (⊤_ C)) B T l) (RelativeCech.ReindexGlobal.rightRefinement f V T t) := by
  have hp := CechPushforward.comparison f F W B J r s V T l t (singleComplex P c) (g+c)
  have ha := MappedSingleCoordinates.comparison (restriction f) P c g F W B J r s V T l t
  have hb := PresheafSingleCoordinates.comparison P c g
    (CechPushforwardCoordinates.pulled f F) W
    ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J)
    (RelativeCech.Reindex.mapped f (F.obj ∘ W) J r) (RelativeCech.Reindex.mapped f B J s)
    ((RelativeCech.ReindexData.preimage f).obj ∘ V) ((RelativeCech.ReindexData.preimage f).obj ∘ T)
    (RelativeCech.ReindexGlobal.leftRefinement f (F.obj (⊤_ C)) B T l) (RelativeCech.ReindexGlobal.rightRefinement f V T t)
  have hu := OrderedCech.ReindexSingle.comparison (RelativeCech.ReindexData.preimage f) V P c g
  exact paste _ _ _
    (Functor.SingleTotal.homologyIso
      (Cech.SingleFunctorCoordinates.localFunctor (CechPushforwardCoordinates.pulled f F) W)
      P c g) _ _ _ _ _ hp ha hb hu

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardSingle

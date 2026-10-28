import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Reindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover

/-! # Cech Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforward

noncomputable section

/-! The complete original principal-to-global comparison commutes
with inverse image of all cover data and pushforward of coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem paste {C : Type*} [Category C] {A B D E B' D' E' : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (a' : A ⟶ B') (b' : B' ⟶ D') (c' : D' ⟶ E')
    (eB : B ⟶ B') (eD : D ⟶ D') (eE : E ⟶ E')
    (ha : a ≫ eB = a') (hb : b ≫ eD = eB ≫ b') (hc : c ≫ eE = eD ≫ c') :
    (a ≫ b ≫ c) ≫ eE = a' ≫ b' ≫ c' := by
  simp only [Category.assoc]
  rw [hc, ← Category.assoc b eD c', hb]
  simp only [Category.assoc]
  rw [← Category.assoc a eB (b' ≫ c'), ha]

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
  (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ D) ℕ) (q : ℕ)
attribute [local instance] RelativeCech.ReindexData.preimage_limits
  CechPushforwardCoordinates.pulled_products

variable
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s (RelativeCech.ReindexTotal.pushed f K) q)]
  [IsIso (RelativeCech.Refinement.homology ((RelativeCech.ReindexData.preimage f).obj (F.obj (⊤_ C)))
    ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J) (RelativeCech.Reindex.mapped f B J s) K q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (RelativeCech.ReindexTotal.pushed f K)) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap ((RelativeCech.ReindexData.preimage f).obj ∘ V)
    ((RelativeCech.ReindexData.preimage f).obj ∘ T) (RelativeCech.ReindexGlobal.rightRefinement f V T t) K) q)]

local instance pulled_relative :
    IsIso (RelativeCech.Refinement.homology
      ((CechPushforwardCoordinates.pulled f F).obj (⊤_ C))
      ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J) (RelativeCech.Reindex.mapped f B J s) K q) :=
  (inferInstance : IsIso (RelativeCech.Refinement.homology ((RelativeCech.ReindexData.preimage f).obj (F.obj (⊤_ C)))
    ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J) (RelativeCech.Reindex.mapped f B J s) K q))

theorem comparison :
    PresheafCover.Comparison.comparison F W B J r s V T l t (RelativeCech.ReindexTotal.pushed f K) q ≫
      homologyMap (OrderedCech.ReindexTotal.totalIso (RelativeCech.ReindexData.preimage f) V K).hom q =
    PresheafCover.Comparison.comparison
      (CechPushforwardCoordinates.pulled f F) W
      ((RelativeCech.ReindexData.preimage f).obj ∘ B) ((RelativeCech.ReindexData.preimage f).obj ∘ J)
      (RelativeCech.Reindex.mapped f (F.obj ∘ W) J r) (RelativeCech.Reindex.mapped f B J s)
      ((RelativeCech.ReindexData.preimage f).obj ∘ V) ((RelativeCech.ReindexData.preimage f).obj ∘ T)
      (RelativeCech.ReindexGlobal.leftRefinement f (F.obj (⊤_ C)) B T l) (RelativeCech.ReindexGlobal.rightRefinement f V T t) K q := by
  exact paste _ _ _ _ _ _ _ _ _
    (CechPushforwardTotal.Coordinates.homology f F W K q)
    (RelativeCech.Reindex.comparison f (F.obj (⊤_ C)) (F.obj ∘ W) B J r s K q)
    (RelativeCech.ReindexGlobal.global_comparison f (F.obj (⊤_ C)) B V T l t K q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforward

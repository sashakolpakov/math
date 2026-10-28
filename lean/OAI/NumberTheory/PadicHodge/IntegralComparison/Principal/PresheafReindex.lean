import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Tail

/-! # Presheaf Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafReindex

noncomputable section

/-! The literal principal-to-global comparison is unchanged by an
actual finite-product-preserving change of principal index category. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} {C D : Type u}
  [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (φ : C ⥤ D) [PreservesFiniteProducts φ] (F : D ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι),
    PreservesLimit (Discrete.functor ((φ.obj ∘ W) ∘ a)) F]
  (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ φ.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (φ.obj (⊤_ C))) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (F.obj (φ.obj (⊤_ C))) B J s K q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t K) q)]

abbrev targetRefinement := Tail.Comparison.refinement
  (F.obj (φ.obj (⊤_ C))) B T l (F.obj (⊤_ D)) (AugmentedCech.AmbientReindex.terminal_eq φ F)

def sourceIso := AugmentedOrdered.CechReindexTotal.totalIso φ W
  (AugmentedCech.AmbientReindex.restricted F K)

omit [HasFiniteProducts D] [PreservesFiniteProducts φ] in
theorem source_isIso :
    IsIso (RelativeCech.Refinement.homology ((φ ⋙ F).obj (⊤_ C)) B J s K q) := by
  change IsIso (RelativeCech.Refinement.homology (F.obj (φ.obj (⊤_ C))) B J s K q)
  infer_instance

theorem comparison :
    letI := source_isIso φ F B J s K q
    letI := Tail.Comparison.relative_isIso (F.obj (φ.obj (⊤_ C))) B J s K q
      (F.obj (⊤_ D)) (AugmentedCech.AmbientReindex.terminal_eq φ F)
    homologyMap (sourceIso φ F W K).hom q ≫
      PresheafCover.Comparison.comparison F (φ.obj ∘ W) B J r s V T
        (targetRefinement φ F B T l) t K q =
    PresheafCover.Comparison.comparison (φ ⋙ F) W B J r s V T l t K q := by
  let := source_isIso φ F B J s K q
  let := Tail.Comparison.relative_isIso (F.obj (φ.obj (⊤_ C))) B J s K q
    (F.obj (⊤_ D)) (AugmentedCech.AmbientReindex.terminal_eq φ F)
  have ha := congrArg (fun b => homologyMap b q)
    (AugmentedCech.AmbientReindex.total φ F W K)
  simp only [homologyMap_comp] at ha
  have ht := Tail.Comparison.transport (F.obj (φ.obj (⊤_ C)))
    (F.obj ∘ φ.obj ∘ W) B J r s V T l t K q (F.obj (⊤_ D))
    (AugmentedCech.AmbientReindex.terminal_eq φ F)
  change homologyMap (sourceIso φ F W K).hom q ≫
      (homologyMap (AugmentedCech.AmbientTotal.totalIso F (φ.obj ∘ W) K).hom q ≫
        Tail.Comparison.map (F.obj (⊤_ D)) (F.obj ∘ φ.obj ∘ W) B J r s V T
          (targetRefinement φ F B T l) t K q) =
    homologyMap (AugmentedCech.AmbientTotal.totalIso (φ ⋙ F) W K).hom q ≫
      Tail.Comparison.map (F.obj (φ.obj (⊤_ C))) (F.obj ∘ φ.obj ∘ W)
        B J r s V T l t K q
  dsimp only [sourceIso]
  erw [← Category.assoc, ha, Category.assoc]
  exact congrArg (fun b => homologyMap
    (AugmentedCech.AmbientTotal.totalIso (φ ⋙ F) W K).hom q ≫ b) ht

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafReindex

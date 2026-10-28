import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PresheafCommonRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology

/-! # Presheaf Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover.Comparison

noncomputable section

/-! The complete principal-to-global map is natural for arbitrary
coefficient-complex maps. Every factor is the original principal
coordinate map, relative refinement, or ordered common-cover map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F]
  (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]

def totalMap {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :=
  HomologicalComplex₂.total.map
    (((AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ)).map
      (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).map a)) (.up ℕ)

def comparison (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) (q : ℕ)
    [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s K q)]
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t K) q)] :=
  (homologyMapIso (AugmentedCech.AmbientTotal.totalIso F W K) q).hom ≫
    Relative.PresheafCommonRefinement.comparison (F.obj (⊤_ C)) (F.obj ∘ W) B J r s K q ≫
      Presheaf.OrderedCover.Comparison.comparison
        (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B) V T l t K q

theorem naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ}
    (a : K ⟶ L) (q : ℕ)
    [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s K q)]
    [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s L q)]
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t K) q)]
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t L) q)] :
    homologyMap (totalMap F W a) q ≫ comparison F W B J r s V T l t L q =
      comparison F W B J r s V T l t K q ≫
        homologyMap ((Presheaf.OrderedCover.Comparison.totalFunctor V).map a) q := by
  have hp := congrArg (fun b => homologyMap b q)
    (AugmentedCech.AmbientTotal.naturality F W K a)
  simp only [homologyMap_comp] at hp
  have hr := Relative.PresheafCommonRefinement.naturality
    (F.obj (⊤_ C)) (F.obj ∘ W) B J r s a q
  have hg := Presheaf.OrderedCover.Comparison.naturality
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B) V T l t a q
  have hpr := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hp hr
  have hh := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hpr hg
  simpa only [comparison, totalMap, homologyMapIso_hom, Category.assoc] using hh

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover.Comparison

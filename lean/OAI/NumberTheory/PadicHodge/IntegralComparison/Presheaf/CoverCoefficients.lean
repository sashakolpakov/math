import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.InverseSquare

/-! # Cover Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CoverCoefficients

noncomputable section

/-! Exact coefficient transport preserves every factor of the original
principal-to-global comparison, including the inverted refinements. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose {D : Type*} [Category D]
    {A B C A' B' C' : D} (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (eA : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C')
    (hf : f ≫ eB = eA ≫ f') (hg : g ≫ eC = eB ≫ g') :
    (f ≫ g) ≫ eC = eA ≫ (f' ≫ g') := by
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

universe u uA vA uB vB
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientHomology
variable {X : TopCat.{u}}
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G] [G.PreservesHomology]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasFiniteBiproducts A]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]

theorem relative_isIso (U : Opens X) (V : ι → Opens X) (T : ν → Opens X)
    (r : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι V) (q : ℕ)
    [IsIso (RelativeCech.Refinement.homology U V T r K q)] :
    IsIso (RelativeCech.Refinement.homology U V T r (IntegralComparison.Principal.CoefficientHomology.mapped G K) q) :=
  Functor.InverseSquare.isIso G (IntegralComparison.Principal.CoefficientHomology.relativeIso G K U V q) (IntegralComparison.Principal.CoefficientHomology.relativeIso G K U T q)
    (RelativeCech.Refinement.homology U V T r K q)
    (RelativeCech.Refinement.homology U V T r (IntegralComparison.Principal.CoefficientHomology.mapped G K) q)
    (IntegralComparison.Principal.CoefficientHomology.refinement G K U V T r q)

theorem relative (U : Opens X) (V : ι → Opens X) (W : κ → Opens X) (T : ν → Opens X)
    (r : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι V)
    (s : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ W) (q : ℕ)
    [IsIso (RelativeCech.Refinement.homology U W T s K q)]
    [IsIso (RelativeCech.Refinement.homology U W T s (IntegralComparison.Principal.CoefficientHomology.mapped G K) q)] :
    G.map (Relative.PresheafCommonRefinement.comparison U V W T r s K q) ≫
        (OrderedCech.CoefficientTotal.homologyIso (RelativeCech.Intersections.cover U W) G K q).hom =
      (IntegralComparison.Principal.CoefficientHomology.relativeIso G K U V q).hom ≫
        Relative.PresheafCommonRefinement.comparison U V W T r s (IntegralComparison.Principal.CoefficientHomology.mapped G K) q := by
  have hi := Functor.InverseSquare.inverse G (IntegralComparison.Principal.CoefficientHomology.relativeIso G K U W q) (IntegralComparison.Principal.CoefficientHomology.relativeIso G K U T q)
    (RelativeCech.Refinement.homology U W T s K q)
    (RelativeCech.Refinement.homology U W T s (IntegralComparison.Principal.CoefficientHomology.mapped G K) q)
    (IntegralComparison.Principal.CoefficientHomology.refinement G K U W T s q)
  have h₁ := compose _ _ _ _ _ _ _ (IntegralComparison.Principal.CoefficientHomology.refinement G K U V T r q) hi
  have h₂ := compose _ _ _ _ _ _ _ h₁ (IntegralComparison.Principal.CoefficientHomology.extension G K U W q)
  simpa only [Relative.PresheafCommonRefinement.comparison, G.map_comp, Category.assoc] using h₂

theorem ordered_isIso (V : ι → Opens X) (T : ν → Opens X)
    (r : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι V) (q : ℕ)
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T r K) q)] :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V T r (IntegralComparison.Principal.CoefficientHomology.mapped G K)) q) :=
  Functor.InverseSquare.isIso G
    (OrderedCech.CoefficientTotal.homologyIso V G K q)
    (OrderedCech.CoefficientTotal.homologyIso T G K q)
    (homologyMap (OrderedCech.Refinement.totalMap V T r K) q)
    (homologyMap (OrderedCech.Refinement.totalMap V T r (IntegralComparison.Principal.CoefficientHomology.mapped G K)) q)
    (Cech.RefinementCoefficientTotal.OrderedCechRefinementCoefficients.homology_natural V T r G K q)

theorem ordered (U : ι → Opens X) (V : κ → Opens X) (T : ν → Opens X)
    (r : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
    (s : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V) (q : ℕ)
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T s K) q)]
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T s (IntegralComparison.Principal.CoefficientHomology.mapped G K)) q)] :
    G.map (OrderedCover.Comparison.comparison U V T r s K q) ≫
        (OrderedCech.CoefficientTotal.homologyIso V G K q).hom =
      (OrderedCech.CoefficientTotal.homologyIso U G K q).hom ≫
        OrderedCover.Comparison.comparison U V T r s (IntegralComparison.Principal.CoefficientHomology.mapped G K) q := by
  have hi := Functor.InverseSquare.inverse G
    (OrderedCech.CoefficientTotal.homologyIso V G K q)
    (OrderedCech.CoefficientTotal.homologyIso T G K q)
    (homologyMap (OrderedCech.Refinement.totalMap V T s K) q)
    (homologyMap (OrderedCech.Refinement.totalMap V T s (IntegralComparison.Principal.CoefficientHomology.mapped G K)) q)
    (Cech.RefinementCoefficientTotal.OrderedCechRefinementCoefficients.homology_natural V T s G K q)
  have h := compose _ _ _ _ _ _ _
    (Cech.RefinementCoefficientTotal.OrderedCechRefinementCoefficients.homology_natural U T r G K q) hi
  simpa only [OrderedCover.Comparison.comparison, G.map_comp] using h

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) (W : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F]
  (C₀ : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ C₀)
  {μ ρ : Type u} [LinearOrder μ] [LinearOrder ρ]
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) C₀))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) C₀ J s K q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t K) q)]

theorem principal :
    letI := relative_isIso G K (F.obj (⊤_ C)) C₀ J s q
    letI := ordered_isIso G K V T t q
    G.map (IntegralComparison.Principal.PresheafCover.Comparison.comparison F W C₀ J r s V T l t K q) ≫
        (OrderedCech.CoefficientTotal.homologyIso V G K q).hom =
      (AugmentedCech.CoefficientTotal.homologyIso W G
        (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K) q).hom ≫
        IntegralComparison.Principal.PresheafCover.Comparison.comparison F W C₀ J r s V T l t (IntegralComparison.Principal.CoefficientHomology.mapped G K) q := by
  let := relative_isIso G K (F.obj (⊤_ C)) C₀ J s q
  let := ordered_isIso G K V T t q
  have h₁ := compose _ _ _ _ _ _ _ (IntegralComparison.Principal.CoefficientHomology.ambient G K F W q)
    (relative G K (F.obj (⊤_ C)) (F.obj ∘ W) C₀ J r s q)
  have h₂ := compose _ _ _ _ _ _ _ h₁
    (ordered G K (RelativeCech.Intersections.cover (F.obj (⊤_ C)) C₀) V T l t q)
  simpa only [IntegralComparison.Principal.PresheafCover.Comparison.comparison, homologyMapIso_hom,
    G.map_comp, Category.assoc] using h₂

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CoverCoefficients

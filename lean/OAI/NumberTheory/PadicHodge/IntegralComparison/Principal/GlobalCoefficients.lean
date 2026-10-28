import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CoverCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficientHomology

/-! # Global Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.GlobalCoefficients

noncomputable section

/-! Exact coefficient change preserves the genuine principal-to-global
map through the inverse of the original ordered global edge. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem global_square {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {L T S : C} {L' T' S' : D}
    (eL : G.obj L ≅ L') (eT : G.obj T ≅ T') (eS : G.obj S ≅ S')
    (c : L ⟶ T) (c' : L' ⟶ T') (a : S ⟶ T) (a' : S' ⟶ T')
    [IsIso a] [IsIso a']
    (hc : G.map c ≫ eT.hom = eL.hom ≫ c')
    (ha : G.map a ≫ eT.hom = eS.hom ≫ a') :
    eL.hom ≫ c' ≫ inv a' ≫ eS.inv = G.map (c ≫ inv a) := by
  have hi := Functor.InverseSquare.inverse G eS eT a a' ha
  apply (cancel_mono eS.hom).mp
  simp only [G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hi, ← Category.assoc (G.map c) eT.hom, hc, Category.assoc]

universe u uA vA uB vB
variable {X : TopCat.{u}}
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  [HasFiniteBiproducts A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology] [PreservesLimitsOfSize.{u,u} G]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)

section Edge
variable {μ : Type u} [LinearOrder μ] (V : μ → Opens X) (q : ℕ)
  [IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V K) q)]

theorem edge_isIso :
    IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V
      (CoefficientHomology.mapped G K)) q) :=
  Functor.InverseSquare.isIso G
    (((Presheaf.OrderedCechEdge.sections K).sc q).mapHomologyIso G).symm
    (OrderedCech.CoefficientTotal.homologyIso V G K q)
    (homologyMap (Presheaf.OrderedCechEdge.edge V K) q)
    (homologyMap (Presheaf.OrderedCechEdge.edge V
      (CoefficientHomology.mapped G K)) q)
    (Ordered.EdgeCoefficientHomology.homology V G K q)

end Edge

variable {C : Type u} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F]
  (B₀ : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B₀)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B₀))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B₀ J s K q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t K) q)]
  [IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V K) q)]

theorem comparison :
    letI := Presheaf.CoverCoefficients.relative_isIso G K (F.obj (⊤_ C)) B₀ J s q
    letI := Presheaf.CoverCoefficients.ordered_isIso G K V T t q
    letI := edge_isIso G K V q
    (AugmentedCech.CoefficientTotal.homologyIso W G
      (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K) q).hom ≫
      PresheafCover.Comparison.comparison F W B₀ J r s V T l t
        (CoefficientHomology.mapped G K) q ≫
      inv (homologyMap (Presheaf.OrderedCechEdge.edge V
        (CoefficientHomology.mapped G K)) q) ≫
      (((Presheaf.OrderedCechEdge.sections K).sc q).mapHomologyIso G).hom =
    G.map (PresheafCover.Comparison.comparison F W B₀ J r s V T l t K q ≫
      inv (homologyMap (Presheaf.OrderedCechEdge.edge V K) q)) := by
  let := Presheaf.CoverCoefficients.relative_isIso G K (F.obj (⊤_ C)) B₀ J s q
  let := Presheaf.CoverCoefficients.ordered_isIso G K V T t q
  let := edge_isIso G K V q
  exact global_square G
    (AugmentedCech.CoefficientTotal.homologyIso W G
      (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K) q)
    (OrderedCech.CoefficientTotal.homologyIso V G K q)
    (((Presheaf.OrderedCechEdge.sections K).sc q).mapHomologyIso G).symm
    (PresheafCover.Comparison.comparison F W B₀ J r s V T l t K q)
    (PresheafCover.Comparison.comparison F W B₀ J r s V T l t
      (CoefficientHomology.mapped G K) q)
    (homologyMap (Presheaf.OrderedCechEdge.edge V K) q)
    (homologyMap (Presheaf.OrderedCechEdge.edge V (CoefficientHomology.mapped G K)) q)
    (Presheaf.CoverCoefficients.principal G K F W B₀ J r s V T l t q)
    (Ordered.EdgeCoefficientHomology.homology V G K q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.GlobalCoefficients

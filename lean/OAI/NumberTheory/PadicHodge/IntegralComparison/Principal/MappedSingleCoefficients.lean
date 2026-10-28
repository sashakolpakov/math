import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CoverCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleCoefficientCoordinates

/-! # Mapped Single Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoefficients

noncomputable section

/-! Exact coefficient change preserves the literal unshifted principal
comparison obtained from the original mapped-single coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem descend {A B : Type*} [Category A] [Category B] (G : A ⥤ B)
    {L T P Q : A} {L' T' P' Q' : B}
    (l : L ≅ P) (t : T ≅ Q) (l' : L' ≅ P') (t' : T' ≅ Q')
    (eL : G.obj L ≅ L') (eT : G.obj T ≅ T')
    (a : L ⟶ T) (a' : L' ⟶ T') (b : P ⟶ Q) (b' : P' ⟶ Q')
    (u : G.obj P ⟶ P') (v : G.obj Q ⟶ Q')
    (ha : a ≫ t.hom = l.hom ≫ b) (ha' : a' ≫ t'.hom = l'.hom ≫ b')
    (hc : G.map a ≫ eT.hom = eL.hom ≫ a')
    (hl : eL.hom ≫ l'.hom = G.map l.hom ≫ u)
    (ht : eT.hom ≫ t'.hom = G.map t.hom ≫ v) :
    G.map b ≫ v = u ≫ b' := by
  apply (cancel_epi (G.map l.hom)).mp
  calc
    G.map l.hom ≫ G.map b ≫ v = G.map a ≫ G.map t.hom ≫ v := by
      rw [← Category.assoc, ← G.map_comp, ← ha, G.map_comp, Category.assoc]
    _ = G.map a ≫ eT.hom ≫ t'.hom := by rw [ht]
    _ = eL.hom ≫ a' ≫ t'.hom := by rw [← Category.assoc, hc, Category.assoc]
    _ = eL.hom ≫ l'.hom ≫ b' := by rw [ha']
    _ = G.map l.hom ≫ u ≫ b' := by rw [← Category.assoc, hl, Category.assoc]

universe u uA vA uB vB uS vS
variable {X : TopCat.{u}}
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  {S : Type uS} [Category.{vS} S] [Abelian S]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology] [PreservesLimitsOfSize.{u,u} G]
  (J : S ⥤ (Opens X)ᵒᵖ ⥤ A) [J.Additive] (M : S) (c g : ℕ)

local instance : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts

abbrev mappedFunctor : S ⥤ (Opens X)ᵒᵖ ⥤ B :=
  J ⋙ (Functor.whiskeringRight (Opens X)ᵒᵖ A B).obj G

variable {C : Type u} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B₀ : κ → Opens X) (E : ν → Opens X)
  (r : FormalCoproduct.mk ν E ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν E ⟶ FormalCoproduct.mk κ B₀)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B₀))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B₀ E s
    (MappedSingleCoordinates.source J M c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (MappedSingleCoordinates.source J M c)) (g+c))]

abbrev localCoefficientIso := AugmentedCech.SingleCoefficientCoordinates.coefficientIso W
  (J ⋙ AugmentedCech.AmbientTotal.restriction F) G M g
abbrev globalCoefficientIso := OrderedCech.SingleCoefficientCoordinates.coefficientIso V J G M g

theorem relative_isIso : IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B₀ E s
    (MappedSingleCoordinates.source (mappedFunctor G J) M c) (g+c)) :=
  Presheaf.CoverCoefficients.relative_isIso G (MappedSingleCoordinates.source J M c)
    (F.obj (⊤_ C)) B₀ E s (g+c)

theorem ordered_isIso : IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (MappedSingleCoordinates.source (mappedFunctor G J) M c)) (g+c)) :=
  Presheaf.CoverCoefficients.ordered_isIso G (MappedSingleCoordinates.source J M c)
    V T t (g+c)

theorem comparison :
    letI := relative_isIso G J M c g F B₀ E s
    letI := ordered_isIso G J M c g V T t
    G.map (MappedSingleCoordinates.coefficientComparison J M c g F W B₀ E r s V T l t) ≫
      (globalCoefficientIso G J M g V).hom =
    (localCoefficientIso G J M g F W).hom ≫
      MappedSingleCoordinates.coefficientComparison (mappedFunctor G J) M c g F W B₀ E r s V T l t := by
  let := relative_isIso G J M c g F B₀ E s
  let := ordered_isIso G J M c g V T t
  apply descend G
    (MappedSingleCoordinates.localCoordinates J M c g F W)
    (MappedSingleCoordinates.globalCoordinates J M c g V)
    (MappedSingleCoordinates.localCoordinates (mappedFunctor G J) M c g F W)
    (MappedSingleCoordinates.globalCoordinates (mappedFunctor G J) M c g V)
    (AugmentedCech.CoefficientTotal.homologyIso W G
      (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj
        (MappedSingleCoordinates.source J M c)) (g+c))
    (OrderedCech.CoefficientTotal.homologyIso V G
      (MappedSingleCoordinates.source J M c) (g+c))
    (PresheafCover.Comparison.comparison F W B₀ E r s V T l t
      (MappedSingleCoordinates.source J M c) (g+c))
    (PresheafCover.Comparison.comparison F W B₀ E r s V T l t
      (MappedSingleCoordinates.source (mappedFunctor G J) M c) (g+c))
  · exact MappedSingleCoordinates.comparison J M c g F W B₀ E r s V T l t
  · exact MappedSingleCoordinates.comparison (mappedFunctor G J) M c g F W B₀ E r s V T l t
  · exact Presheaf.CoverCoefficients.principal G (MappedSingleCoordinates.source J M c)
      F W B₀ E r s V T l t (g+c)
  · exact AugmentedCech.SingleCoefficientCoordinates.comparison W
      (J ⋙ AugmentedCech.AmbientTotal.restriction F) G M c g
  · exact OrderedCech.SingleCoefficientCoordinates.comparison V J G M c g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoefficients

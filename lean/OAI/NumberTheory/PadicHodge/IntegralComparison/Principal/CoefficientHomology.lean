import OAI.NumberTheory.PadicHodge.IntegralComparison.AmbientCechCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ExtensionCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementCoefficientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare

/-! # Coefficient Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientHomology

noncomputable section

/-! The original exact-functor homology coordinates for the ambient,
relative-extension, and complementary-refinement coefficient squares. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB
variable {X : TopCat.{u}}
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G] [G.PreservesHomology]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasFiniteBiproducts A]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)

abbrev mapped := AugmentedCech.CoefficientTotal.mapped G K

def relativeIso (U : Opens X) {ι : Type u} [LinearOrder ι] (V : ι → Opens X) (q : ℕ) :=
  Functor.HomologySquare.iso G (RelativeCech.CoefficientTotal.iso U V G K) q

theorem extension (U : Opens X) {ι : Type u} [LinearOrder ι] (V : ι → Opens X) (q : ℕ) :
    G.map (homologyMap (RelativeCech.Total.map U V K) q) ≫
        (OrderedCech.CoefficientTotal.homologyIso (RelativeCech.Intersections.cover U V) G K q).hom =
      (relativeIso G K U V q).hom ≫
        homologyMap (RelativeCech.Total.map U V (mapped G K)) q :=
  Functor.HomologySquare.naturality G
    (RelativeCech.Total.map U V K) (RelativeCech.Total.map U V (mapped G K))
    (RelativeCech.CoefficientTotal.iso U V G K)
    (OrderedCech.CoefficientTotal.totalIso (RelativeCech.Intersections.cover U V) G K)
    (Relative.ExtensionCoefficient.total U V G K) q

theorem refinement (U : Opens X) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
    (V : ι → Opens X) (W : κ → Opens X)
    (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V) (q : ℕ) :
    G.map (RelativeCech.Refinement.homology U V W r K q) ≫
      (relativeIso G K U W q).hom =
    (relativeIso G K U V q).hom ≫
      RelativeCech.Refinement.homology U V W r (mapped G K) q :=
  Cech.RefinementCoefficientTotal.AugmentedCechRefinementCoefficients.homology_natural V W r G
    (((RelativeCech.Refinement.restriction U).mapHomologicalComplex (.up ℕ)).obj K) q

theorem ambient {C : Type u} [Preorder C] [HasFiniteProducts C]
    (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C)
    [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F] (q : ℕ) :
    G.map (homologyMap (AugmentedCech.AmbientTotal.totalIso F U K).hom q) ≫
        (relativeIso G K (F.obj (⊤_ C)) (F.obj ∘ U) q).hom =
      (AugmentedCech.CoefficientTotal.homologyIso U G
        (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K) q).hom ≫
        homologyMap (AugmentedCech.AmbientTotal.totalIso F U (mapped G K)).hom q :=
  Functor.HomologySquare.naturality G
    (AugmentedCech.AmbientTotal.totalIso F U K).hom
    (AugmentedCech.AmbientTotal.totalIso F U (mapped G K)).hom
    (AugmentedCech.CoefficientTotal.totalIso U G
      (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K))
    (RelativeCech.CoefficientTotal.iso (F.obj (⊤_ C)) (F.obj ∘ U) G K)
    (AmbientCechCoefficient.total F U G K) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientHomology

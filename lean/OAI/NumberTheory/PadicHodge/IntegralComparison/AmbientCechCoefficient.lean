import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientSquare

/-! # Ambient Cech Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AmbientCechCoefficient

noncomputable section

/-! Coefficient transport commutes with the original identification
between principal supported cochains and ambient relative cochains. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB
variable {X : TopCat.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  (P : (Opens X)ᵒᵖ ⥤ A)

omit [Abelian A] [Abelian B] [G.Additive] in
theorem component (n : ℕ) :
    G.map (AugmentedCech.AmbientCoordinates.componentIso F U P n).hom ≫
      (AugmentedCech.CoefficientChange.objectIso (F.obj ∘ U) G
        ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op ⋙ P) n).hom =
    (AugmentedCech.CoefficientChange.objectIso U G (F.op ⋙ P) n).hom ≫
      (AugmentedCech.AmbientCoordinates.componentIso F U (P ⋙ G) n).hom :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map G
    (fun a : AugmentedOrdered.Cech.Index ι n => P.map (AugmentedCech.AmbientCoordinates.objectIso F U n a).inv.op)

theorem complex :
    (G.mapHomologicalComplex (.up ℕ)).map (AugmentedCech.AmbientCoordinates.iso F U P).hom ≫
      (AugmentedCech.CoefficientChange.complexIso (F.obj ∘ U) G
        ((RelativeCech.Intersections.intersect (F.obj (⊤_ C))).op ⋙ P)).hom =
    (AugmentedCech.CoefficientChange.complexIso U G (F.op ⋙ P)).hom ≫
      (AugmentedCech.AmbientCoordinates.iso F U (P ⋙ G)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact component F U G P n

variable [HasCoproducts.{0} A] [HasCoproducts.{0} B]
local instance finiteBiproducts : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)

omit [HasCoproducts A] [HasCoproducts B] in
theorem bicomplex :
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (AugmentedCech.AmbientTotal.bicomplexIso F U K).hom ≫
      (AugmentedCech.CoefficientTotal.bicomplexIso (F.obj ∘ U) G
        (((RelativeCech.Refinement.restriction (F.obj (⊤_ C))).mapHomologicalComplex (.up ℕ)).obj K)).hom =
    (AugmentedCech.CoefficientTotal.bicomplexIso U G
      (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K)).hom ≫
      (AugmentedCech.AmbientTotal.bicomplexIso F U
        (AugmentedCech.CoefficientTotal.mapped G K)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact complex F U G (K.X n)

theorem total :
    (G.mapHomologicalComplex (.up ℕ)).map (AugmentedCech.AmbientTotal.totalIso F U K).hom ≫
      (RelativeCech.CoefficientTotal.iso (F.obj (⊤_ C)) (F.obj ∘ U) G K).hom =
    (AugmentedCech.CoefficientTotal.totalIso U G
      (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K)).hom ≫
      (AugmentedCech.AmbientTotal.totalIso F U (AugmentedCech.CoefficientTotal.mapped G K)).hom :=
  Finite.TotalCoefficientSquare.comparison G
    (AugmentedCech.CoefficientTotal.bicomplexIso U G
      (((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K))
    (AugmentedCech.CoefficientTotal.bicomplexIso (F.obj ∘ U) G
      (((RelativeCech.Refinement.restriction (F.obj (⊤_ C))).mapHomologicalComplex (.up ℕ)).obj K))
    (AugmentedCech.AmbientTotal.bicomplexIso F U K).hom
    (AugmentedCech.AmbientTotal.bicomplexIso F U (AugmentedCech.CoefficientTotal.mapped G K)).hom
    (bicomplex F U G K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AmbientCechCoefficient

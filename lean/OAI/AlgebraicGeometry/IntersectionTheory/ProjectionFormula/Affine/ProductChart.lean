import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecScalarSections
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Product Chart -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ProductChart

noncomputable section

/-! An actual affine product chart is the spectrum of the tensor
product of the two affine section rings over the given scalar field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] {X Y : Scheme}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)

def inclusion :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))))
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(Y, V)))) ⟶ pullback f g := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
  exact pullback.map _ _ f g hU.fromSpec hV.fromSpec (𝟙 _)
    ((Category.comp_id _).trans (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU))
    ((Category.comp_id _).trans (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec g V hV))

theorem inclusion_open :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
    IsOpenImmersion (inclusion f g U hU V hV) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion hU.fromSpec)) (inferInstanceAs (IsOpenImmersion hV.fromSpec))
    (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU) (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec g V hV)

def map :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
    Spec (.of (Γ(X, U) ⊗[K] Γ(Y, V))) ⟶ pullback f g := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
  exact (pullbackSpecIso K Γ(X, U) Γ(Y, V)).inv ≫ inclusion f g U hU V hV

theorem isOpenImmersion :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
    IsOpenImmersion (ProductChart.map f g U hU V hV) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
  let := inclusion_open f g U hU V hV
  unfold ProductChart.map
  infer_instance

theorem range :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
    Set.range (ProductChart.map f g U hU V hV) =
      pullback.fst f g ⁻¹' (U : Set X) ∩ pullback.snd f g ⁻¹' (V : Set Y) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
  change Set.range (inclusion f g U hU V hV ∘ (pullbackSpecIso K Γ(X, U) Γ(Y, V)).inv) = _
  rw [Set.range_comp, (pullbackSpecIso K Γ(X, U) Γ(Y, V)).inv.surjective.range_eq, Set.image_univ,
    inclusion, Scheme.Pullback.range_map]
  exact congrArg₂ (fun S : Set X => fun T : Set Y =>
    pullback.fst f g ⁻¹' S ∩ pullback.snd f g ⁻¹' T) hU.range_fromSpec hV.range_fromSpec

theorem over_base :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
    ProductChart.map f g U hU V hV ≫ pullback.fst f g ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K (Γ(X, U) ⊗[K] Γ(Y, V)))) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
  rw [ProductChart.map, Category.assoc, inclusion, pullback.lift_fst_assoc,
    Category.assoc, ← Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU]
  have he := congrArg (fun a => (pullbackSpecIso K Γ(X, U) Γ(Y, V)).inv ≫ a)
    (pullbackSpecIso_hom_base K Γ(X, U) Γ(Y, V))
  rw [Iso.inv_hom_id_assoc] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ProductChart

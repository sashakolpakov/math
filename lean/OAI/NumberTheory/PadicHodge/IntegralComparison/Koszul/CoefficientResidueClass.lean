import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLargeTop

/-! # Coefficient Residue Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidueClass

noncomputable section

/-! The supported mixed Koszul fraction maps to its literal coefficient
residue in the original augmented total cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

private theorem projection_inclusion
    {C : Type u} [Preorder C] [HasFiniteProducts C]
    {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
    {R : Type u} [CommRing R] (N : Cᵒᵖ ⥤ ModuleCat.{u} R)
    (m : ℕ) (hm : Fintype.card ι = m) :
    Pi.π (fun a : AugmentedOrdered.Cech.Index ι m => N.obj (op ((AugmentedOrdered.Cech.formal U m).obj a))) (AugmentedOrdered.CechCoordinates.topIndex m hm) ≫
      AugmentedOrdered.CechCoordinates.topInclusion U N m hm = 𝟙 _ := by
  apply Pi.hom_ext
  intro a
  obtain rfl := AugmentedOrdered.CechCoordinates.topIndex_unique m hm a
  change (_ ≫ AugmentedOrdered.CechCoordinates.topInclusion U N m hm) ≫
    Pi.π (fun a : AugmentedOrdered.Cech.Index ι m => N.obj (op ((AugmentedOrdered.Cech.formal U m).obj a))) (AugmentedOrdered.CechCoordinates.topIndex m hm) = _
  have h := AugmentedOrdered.CechCoordinates.topInclusion_comp_pi U N m hm (AugmentedOrdered.CechCoordinates.topIndex m hm)
  have hi : N.map (AugmentedOrdered.CechCoordinates.topFactorIso U m hm (AugmentedOrdered.CechCoordinates.topIndex m hm)).inv.op =
      𝟙 (N.obj (op (AugmentedOrdered.CechCoordinates.topObject U m hm))) := by
    change N.map (𝟙 (op (AugmentedOrdered.CechCoordinates.topObject U m hm))) = _
    exact N.map_id _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => Pi.π (fun a : AugmentedOrdered.Cech.Index ι m =>
      N.obj (op ((AugmentedOrdered.Cech.formal U m).obj a))) (AugmentedOrdered.CechCoordinates.topIndex m hm) ≫ z) (h.trans hi)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (N : Cᵒᵖ ⥤ ModuleCat.{u} R) (α : KoszulPartial.Fractions.modules R P ⟶ N)
  (hN : ∀ (a : Cᵒᵖ) (i : Fin c) (x : N.obj a), s i • x = 0)

private theorem cardinal : Fintype.card (ULift.{u} (Fin m)) = m := by simp
local notation "hm" => OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidueClass.cardinal (m := m)
local notation "a₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates.topIndex m hm
local notation "o₀" => op (OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates.topObject U m hm)
abbrev residueTarget : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  (single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).obj N
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidueClass.residueTarget R (c := c) N

/-- Literal oriented residue coefficient, inserted in the sole coefficient degree. -/
def residueValue
    (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    ((L).X c).obj o₀ :=
  (singleObjXSelf (.up ℕ) c N).inv.app o₀
    (α.app o₀ ((show P.obj o₀ from KoszulPartial.Fractions.reciprocal R P U t ht a₀) * algebraMap R (P.obj o₀)
      (φ (TopExteriorCoordinates.generator
        (KoszulPartial.TopResidue.basis R (c := c) (m := m))))))

theorem residueValue_closed
    (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    ((L).d c (c+1)).app o₀ (residueValue R P U t ht N α φ) = 0 := by
  rw [single_obj_d]
  rfl

include hN in
theorem residue_top
    (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    ((CoefficientResidue.complexMap R P s N α hN).f c).app o₀
      (KoszulPartial.Components.coordinateAt R P U t ht (c+m) c m rfl a₀ φ) =
    residueValue R P U t ht N α φ := by
  have he : (CoefficientResidue.complexMap R P s N α hN).f c =
      CoefficientResidue.evaluation R P s N α ≫ (singleObjXSelf (.up ℕ) c N).inv := by
    apply (cancel_mono (singleObjXSelf (.up ℕ) c N).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, CoefficientResidue.complexMap_top]
  change ((CoefficientResidue.complexMap R P s N α hN).f c).app o₀ _ = _
  rw [he]
  change (singleObjXSelf (.up ℕ) c N).inv.app o₀
    ((CoefficientResidue.evaluation R P s N α).app o₀ _) = _
  exact congrArg ((singleObjXSelf (.up ℕ) c N).inv.app o₀)
    (CoefficientResidue.fraction R P s N α U t ht a₀ φ)

include hN in
theorem mapped_cycle
    (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    IntegralComparison.Module.CochainClassNaturality.cycleMap (AugmentedOrdered.CechTopNaturality.totalMap U (CoefficientResidue.complexMap R P s N α hN)) (c+m)
      (KoszulPartial.PartialClass.supportedCycle R P U s t ht φ) =
    AugmentedOrdered.CechLargeTop.topTotalCycle U L m hm c
      (residueValue R P U t ht N α φ) (residueValue_closed R P U t ht N α φ) := by
  apply Subtype.ext
  change (AugmentedOrdered.CechTopNaturality.totalMap U (CoefficientResidue.complexMap R P s N α hN)).f (c+m)
      (KoszulPartial.PartialClass.supportedCycle R P U s t ht φ).val = _
  rw [KoszulPartial.PartialClass.supportedCycle_val]
  have hι := ConcreteCategory.congr_hom
    (HomologicalComplex₂.ιTotal_map _ _
      (AugmentedOrdered.CechTopNaturality.bicomplexMap U (CoefficientResidue.complexMap R P s N α hN)) (.up ℕ) c m (c+m) rfl)
      (KoszulPartial.Components.component R P U t ht (c+m) c m rfl φ)
  change (AugmentedOrdered.CechTopNaturality.totalMap U (CoefficientResidue.complexMap R P s N α hN)).f (c+m)
      ((KoszulPartial.Components.target R P U s).ιTotal (.up ℕ) c m (c+m) rfl _) = _ at hι
  rw [hι]
  change (AugmentedOrdered.CechFunctor.bicomplex U L).ιTotal (.up ℕ) c m (c+m) rfl
      (AugmentedOrdered.CechFunctor.objectMap U ((CoefficientResidue.complexMap R P s N α hN).f c) m
        (KoszulPartial.Components.component R P U t ht (c+m) c m rfl φ)) =
    (AugmentedOrdered.CechFunctor.bicomplex U L).ιTotal (.up ℕ) c m (c+m) rfl
      (AugmentedOrdered.CechCoordinates.topInclusion U ((L).X c) m hm (residueValue R P U t ht N α φ))
  congr 1
  let y := AugmentedOrdered.CechFunctor.objectMap U ((CoefficientResidue.complexMap R P s N α hN).f c) m
    (KoszulPartial.Components.component R P U t ht (c+m) c m rfl φ)
  have hy := ConcreteCategory.congr_hom (projection_inclusion U ((L).X c) m hm) y
  change AugmentedOrdered.CechCoordinates.topInclusion U ((L).X c) m hm
    (Pi.π (fun a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m =>
      ((L).X c).obj (op ((AugmentedOrdered.Cech.formal U m).obj a))) a₀ y) = y at hy
  change y = AugmentedOrdered.CechCoordinates.topInclusion U ((L).X c) m hm (residueValue R P U t ht N α φ)
  apply hy.symm.trans
  apply congrArg (AugmentedOrdered.CechCoordinates.topInclusion U ((L).X c) m hm)
  have hx := ConcreteCategory.congr_hom
    (AugmentedOrdered.CechCoordinates.objectMap_comp_pi U ((KoszulPartial.Components.coefficient R P s).X c)
      ((CoefficientResidue.complexMap R P s N α hN).f c) m a₀)
    (KoszulPartial.Components.component R P U t ht (c+m) c m rfl φ)
  have hc := ConcreteCategory.congr_hom
    (KoszulPartial.Components.component_projection R P U s t ht (c+m) c m rfl a₀) φ
  exact hx.trans ((congrArg (((CoefficientResidue.complexMap R P s N α hN).f c).app o₀) hc).trans
    (residue_top R P U s t ht N α hN φ))

include hN in
theorem supportedClass_residue
    (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    homologyMap (AugmentedOrdered.CechTopNaturality.totalMap U (CoefficientResidue.complexMap R P s N α hN)) (c+m)
      (KoszulPartial.PartialClass.supportedClass R P U s t ht φ) =
    AugmentedOrdered.CechLargeTop.topTotalClass U L m hm c
      (residueValue R P U t ht N α φ) (residueValue_closed R P U t ht N α φ) := by
  rw [KoszulPartial.PartialClass.supportedClass, ← IntegralComparison.Module.CochainClassNaturality.naturality_apply,
    mapped_cycle]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidueClass

import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopCycleBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientChange

/-! # Top Class Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassMap

noncomputable section

/-! The full-intersection class as an actual morphism, natural in
coefficients and principal reindexing. This gives the same concrete
module class and applies unchanged after forgetting scalars. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopClass OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem short_natural {A : Type*} [Category A] [Abelian A]
    {S T : ShortComplex A} (f : S ⟶ T) (hS : S.g = 0) (hT : T.g = 0) :
    TopHomologyCokernel.shortClass S hS ≫ ShortComplex.homologyMap f = f.τ₂ ≫ TopHomologyCokernel.shortClass T hT := by
  apply (cancel_mono (TopHomologyCokernel.shortIso T hT).hom).mp
  rw [Category.assoc, TopHomologyCokernel.short_naturality f hS hT, ← Category.assoc,
    TopHomologyCokernel.shortClass_iso S hS, Category.assoc, TopHomologyCokernel.shortClass_iso T hT, cokernel.π_desc]

universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{u} A]
  (P : Cᵒᵖ ⥤ A) (m : ℕ) (hm : Fintype.card ι = m)

include hm in
theorem outgoing : ((AugmentedOrdered.Cech.complex U P).sc m).g = 0 := by
  change (AugmentedOrdered.Cech.complex U P).d m ((ComplexShape.up ℕ).next m) = 0
  rw [CochainComplex.next]
  dsimp only [AugmentedOrdered.Cech.complex]
  rw [CochainComplex.of_d, AugmentedOrdered.CechCoordinates.differential_top U P m hm]

def map : P.obj (op (AugmentedOrdered.CechCoordinates.topObject U m hm)) ⟶ (AugmentedOrdered.Cech.complex U P).homology m :=
  AugmentedOrdered.CechCoordinates.topInclusion U P m hm ≫ TopHomologyCokernel.shortClass ((AugmentedOrdered.Cech.complex U P).sc m) (outgoing U P m hm)

theorem naturality {Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    TopClassMap.map U P m hm ≫ homologyMap (AugmentedOrdered.CechFunctor.complexMap U f) m =
      f.app (op (AugmentedOrdered.CechCoordinates.topObject U m hm)) ≫ TopClassMap.map U Q m hm := by
  have h := short_natural ((shortComplexFunctor A (.up ℕ) m).map (AugmentedOrdered.CechFunctor.complexMap U f))
    (outgoing U P m hm) (outgoing U Q m hm)
  change TopHomologyCokernel.shortClass ((AugmentedOrdered.Cech.complex U P).sc m) (outgoing U P m hm) ≫ homologyMap (AugmentedOrdered.CechFunctor.complexMap U f) m =
    (AugmentedOrdered.CechFunctor.complexMap U f).f m ≫ TopHomologyCokernel.shortClass ((AugmentedOrdered.Cech.complex U Q).sc m) (outgoing U Q m hm) at h
  rw [TopClassMap.map, TopClassMap.map, Category.assoc, h, ← Category.assoc]
  change (AugmentedOrdered.CechCoordinates.topInclusion U P m hm ≫ AugmentedOrdered.CechFunctor.objectMap U f m) ≫ _ = _
  rw [AugmentedOrdered.CechCoordinates.topInclusion_naturality, Category.assoc]

variable {D : Type u} [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r] (Q : Dᵒᵖ ⥤ A)

theorem reindex :
    TopClassMap.map U (r.op ⋙ Q) m hm ≫ homologyMap (AugmentedOrdered.CechReindex.iso r U Q).hom m =
      AugmentedOrdered.CechReindexTop.coefficient r U m hm Q ≫ TopClassMap.map (r.obj ∘ U) Q m hm := by
  have h := short_natural ((shortComplexFunctor A (.up ℕ) m).map
    (AugmentedOrdered.CechReindex.iso r U Q).hom)
    (outgoing U (r.op ⋙ Q) m hm) (outgoing (r.obj ∘ U) Q m hm)
  change TopHomologyCokernel.shortClass ((AugmentedOrdered.Cech.complex U (r.op ⋙ Q)).sc m) (outgoing U (r.op ⋙ Q) m hm) ≫
    homologyMap (AugmentedOrdered.CechReindex.iso r U Q).hom m =
    (AugmentedOrdered.CechReindex.iso r U Q).hom.f m ≫
      TopHomologyCokernel.shortClass ((AugmentedOrdered.Cech.complex (r.obj ∘ U) Q).sc m) (outgoing (r.obj ∘ U) Q m hm) at h
  rw [TopClassMap.map, TopClassMap.map, Category.assoc, h, ← Category.assoc]
  simpa only [Category.assoc, AugmentedOrdered.CechReindex.hom_f] using
    congrArg (fun a => a ≫ TopHomologyCokernel.shortClass ((AugmentedOrdered.Cech.complex (r.obj ∘ U) Q).sc m)
      (outgoing (r.obj ∘ U) Q m hm))
      (AugmentedOrdered.CechReindexTop.inclusion r U m hm Q)

variable {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  (N : Cᵒᵖ ⥤ ModuleCat.{w} R)

theorem module_apply (z : N.obj (op (AugmentedOrdered.CechCoordinates.topObject U m hm))) :
    TopClassMap.map U N m hm z = AugmentedOrdered.CechTopClass.topClass U N m hm z := by
  let K := AugmentedOrdered.Cech.complex U N
  let x := AugmentedOrdered.CechTopClass.topCycle U N m hm z
  have hc : ((K.sc m).cyclesIsoX₂ (outgoing U N m hm)).inv (AugmentedOrdered.CechCoordinates.topInclusion U N m hm z) =
      (IntegralComparison.Module.CochainClassNaturality.cyclesIso K m).hom x := by
    apply (ModuleCat.mono_iff_injective (K.iCycles m)).mp inferInstance
    have h₁ := ConcreteCategory.congr_hom
      ((K.sc m).cyclesIsoX₂_inv_hom_id (outgoing U N m hm)) (AugmentedOrdered.CechCoordinates.topInclusion U N m hm z)
    have h₂ := ConcreteCategory.congr_hom
      (IntegralComparison.Module.CochainClassNaturality.cyclesIso_hom_i K m) x
    exact h₁.trans h₂.symm
  have hclass := ConcreteCategory.congr_hom
    (IntegralComparison.Module.CochainClassNaturality.classMap_eq K m) x
  change K.homologyπ m (((K.sc m).cyclesIsoX₂ (outgoing U N m hm)).inv
      (AugmentedOrdered.CechCoordinates.topInclusion U N m hm z)) = _
  exact (congrArg (K.homologyπ m) hc).trans hclass.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassMap

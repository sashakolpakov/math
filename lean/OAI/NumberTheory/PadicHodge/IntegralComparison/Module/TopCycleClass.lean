import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel

/-! # Top Cycle Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TopCycleClass

noncomputable section

/-! Concrete top cocycles use the original categorical homology projection. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
  (h : IsZero (K.X ((ComplexShape.up ℕ).next n)))

 theorem comparison :
    ModuleCat.ofHom (X := ModuleCat.of R (CochainClasses.cycles K n))
      (Y := K.homology n) (CochainClasses.classMap K n) =
    ModuleCat.ofHom (X := ModuleCat.of R (CochainClasses.cycles K n))
      (Y := K.X n) (CochainClasses.cycles K n).subtype ≫
        TopHomologyCokernel.cycleClass K n h := by
  rw [CochainClassNaturality.classMap_eq]
  dsimp only [TopHomologyCokernel.cycleClass, TopHomologyCokernel.shortClass]
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (K.iCycles n)).mp
  rw [CochainClassNaturality.cyclesIso_hom_i, Category.assoc]
  simp only [HomologicalComplex.iCycles, ShortComplex.cyclesIsoX₂_inv_hom_id]
  exact (Category.comp_id _).symm

 theorem apply (x : CochainClasses.cycles K n) :
    CochainClasses.classMap K n x =
      TopHomologyCokernel.cycleClass K n h x.val :=
  ConcreteCategory.congr_hom (comparison K n h) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TopCycleClass

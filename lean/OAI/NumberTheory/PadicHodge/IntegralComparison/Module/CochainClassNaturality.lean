import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

/-! # Cochain Class Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

noncomputable section

/-! The concrete cycle-class map is the native homology projection and is natural in the complex. -/

open _root_.CategoryTheory Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

universe u v

variable {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{v} R) ℕ)

def cyclesIso (n : ℕ) : ModuleCat.of R (CochainClasses.cycles K n) ≅ K.cycles n :=
  (CochainClasses.short K n).moduleCatCyclesIso.symm ≪≫
    (K.cyclesIsoSc' ((ComplexShape.up ℕ).prev n) n (n + 1) rfl (CochainComplex.next ℕ n)).symm

theorem cyclesIso_hom_i (n : ℕ) :
    (cyclesIso K n).hom ≫ K.iCycles n =
      ModuleCat.ofHom (X := ModuleCat.of R (CochainClasses.cycles K n)) (Y := K.X n) (CochainClasses.cycles K n).subtype := by
  change ((CochainClasses.short K n).moduleCatCyclesIso.inv ≫
    (K.cyclesIsoSc' ((ComplexShape.up ℕ).prev n) n (n + 1) rfl (CochainComplex.next ℕ n)).inv) ≫
      K.iCycles n = _
  rw [Category.assoc, K.cyclesIsoSc'_inv_iCycles]
  exact (CochainClasses.short K n).moduleCatCyclesIso_inv_iCycles

theorem classMap_eq (n : ℕ) :
    ModuleCat.ofHom (X := ModuleCat.of R (CochainClasses.cycles K n)) (Y := K.homology n) (CochainClasses.classMap K n) =
      (cyclesIso K n).hom ≫ K.homologyπ n := by
  symm
  change ((CochainClasses.short K n).moduleCatCyclesIso.inv ≫
    (K.cyclesIsoSc' ((ComplexShape.up ℕ).prev n) n (n + 1) rfl (CochainComplex.next ℕ n)).inv) ≫
      K.homologyπ n = _
  rw [Category.assoc, ← K.π_homologyIsoSc'_inv, ← Category.assoc,
    (CochainClasses.short K n).moduleCatCyclesIso_inv_π]
  rfl

variable {K} {L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)

def cycleMap (n : ℕ) : CochainClasses.cycles K n →ₗ[R] CochainClasses.cycles L n :=
  ((f.f n).hom.comp (CochainClasses.cycles K n).subtype).codRestrict _ (fun x => by
    have h := congrArg (fun g => g x.val) (f.comm n (n + 1))
    change L.d n (n + 1) (f.f n x.val) = f.f (n + 1) (K.d n (n + 1) x.val) at h
    exact h.trans (by rw [x.property, map_zero]))

theorem cycleMap_iso (n : ℕ) :
    ModuleCat.ofHom (X := ModuleCat.of R (CochainClasses.cycles K n)) (Y := ModuleCat.of R (CochainClasses.cycles L n)) (cycleMap f n) ≫
      (cyclesIso L n).hom = (cyclesIso K n).hom ≫ HomologicalComplex.cyclesMap f n := by
  apply (cancel_mono (L.iCycles n)).mp
  rw [Category.assoc, cyclesIso_hom_i, Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, cyclesIso_hom_i]
  rfl

theorem naturality (n : ℕ) :
    ModuleCat.ofHom (X := ModuleCat.of R (CochainClasses.cycles K n)) (Y := ModuleCat.of R (CochainClasses.cycles L n)) (cycleMap f n) ≫
      ModuleCat.ofHom (X := ModuleCat.of R (CochainClasses.cycles L n)) (Y := L.homology n) (CochainClasses.classMap L n) =
    ModuleCat.ofHom (X := ModuleCat.of R (CochainClasses.cycles K n)) (Y := K.homology n) (CochainClasses.classMap K n) ≫
      HomologicalComplex.homologyMap f n := by
  rw [classMap_eq, classMap_eq, ← Category.assoc, cycleMap_iso, Category.assoc,
    ← HomologicalComplex.homologyπ_naturality, Category.assoc]

theorem naturality_apply (n : ℕ) (x : CochainClasses.cycles K n) :
    CochainClasses.classMap L n (cycleMap f n x) = HomologicalComplex.homologyMap f n (CochainClasses.classMap K n x) :=
  congrArg (fun g => g x) (naturality f n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

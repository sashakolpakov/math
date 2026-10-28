import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.Head

/-! # Zero Cycles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroCycles.CochainZeroCycles

noncomputable section

/-! Degree-zero quasi-isomorphisms give actual isomorphisms of differential kernels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable {C D : CochainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D)

theorem cycles_iso [QuasiIsoAt φ 0] : IsIso (HomologicalComplex.cyclesMap φ 0) := by
  have : IsIso (HomologicalComplex.cyclesMap φ 0 ≫ D.homologyπ 0) := by
    rw [← HomologicalComplex.homologyπ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right (HomologicalComplex.cyclesMap φ 0) (D.homologyπ 0)

def cyclesIso (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    C.cycles 0 ≅ ModuleCat.of R (C.d 0 1).hom.ker :=
  C.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫ (C.sc' 0 0 1).moduleCatCyclesIso

theorem cyclesIso_hom_subtype (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    (cyclesIso C).hom ≫ ModuleCat.ofHom (C.d 0 1).hom.ker.subtype = C.iCycles 0 := by
  exact (Category.assoc (C.cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom
    (C.sc' 0 0 1).moduleCatCyclesIso.hom (C.sc' 0 0 1).moduleCatLeftHomologyData.i).trans
    ((congrArg (fun k : (C.sc' 0 0 1).cycles ⟶ C.X 0 =>
      (C.cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom ≫ k)
      (C.sc' 0 0 1).moduleCatCyclesIso_hom_i).trans
      (C.cyclesIsoSc'_hom_iCycles 0 0 1 (by simp) (by simp)))

theorem cyclesIso_inv_iCycles (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    (cyclesIso C).inv ≫ C.iCycles 0 = ModuleCat.ofHom (C.d 0 1).hom.ker.subtype := by
  rw [← cyclesIso_hom_subtype, Iso.inv_hom_id_assoc]

def kernelEquiv [QuasiIsoAt φ 0] : (C.d 0 1).hom.ker ≃ₗ[R] (D.d 0 1).hom.ker := by
  have := cycles_iso φ
  exact ((cyclesIso C).symm ≪≫ asIso (HomologicalComplex.cyclesMap φ 0) ≪≫
    cyclesIso D).toLinearEquiv

theorem kernelEquiv_apply_val [QuasiIsoAt φ 0] (x : (C.d 0 1).hom.ker) :
    (kernelEquiv φ x).val = φ.f 0 x.val := by
  have he : (cyclesIso C).inv ≫ HomologicalComplex.cyclesMap φ 0 ≫
      (cyclesIso D).hom ≫ ModuleCat.ofHom (D.d 0 1).hom.ker.subtype =
        ModuleCat.ofHom (C.d 0 1).hom.ker.subtype ≫ φ.f 0 := by
    rw [cyclesIso_hom_subtype, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, cyclesIso_inv_iCycles]
  exact ConcreteCategory.congr_hom he x

variable {A : ModuleCat.{v} R} (d : A ⟶ D.X 0) (hd : d ≫ D.d 0 1 = 0)

def lift [QuasiIsoAt φ 0] : A ⟶ C.X 0 :=
  ModuleCat.ofHom ((C.d 0 1).hom.ker.subtype.comp
    ((kernelEquiv φ).symm.toLinearMap.comp
      (d.hom.codRestrict _ (fun x => by
        change (d ≫ D.d 0 1) x = 0
        rw [hd]
        rfl))))

theorem lift_zero [QuasiIsoAt φ 0] : lift φ d hd ≫ C.d 0 1 = 0 := by
  ext x
  exact ((kernelEquiv φ).symm ⟨d x, by
    change (d ≫ D.d 0 1) x = 0
    rw [hd]
    rfl⟩).property

theorem lift_comp [QuasiIsoAt φ 0] : lift φ d hd ≫ φ.f 0 = d := by
  ext x
  let y : (D.d 0 1).hom.ker := ⟨d x, by
    change (d ≫ D.d 0 1) x = 0
    rw [hd]
    rfl⟩
  change φ.f 0 ((kernelEquiv φ).symm y).val = d x
  rw [← kernelEquiv_apply_val, LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroCycles.CochainZeroCycles

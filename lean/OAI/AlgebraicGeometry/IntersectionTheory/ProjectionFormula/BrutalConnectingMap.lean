import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltrationQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitSequenceCochain

/-! # Brutal Connecting Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalConnectingMap

noncomputable section

/-! The connecting cochain between adjacent columns of the tail filtration. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex _root_.CochainComplex.HomComplex

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltration OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltrationQuotient

variable (R : Type) [CommRing R] (A : CochainComplex (ModuleCat.{0} R) ℤ) (p : ℤ)

def retraction (n : ℤ) : (BrutalFiltration.complex R A ((p + 1 : ℤ) : EInt)).X n ⟶ (BrutalFiltration.complex R A (p : EInt)).X n :=
  (BrutalFiltrationQuotient.splitting R A p n).r

def sectionMap (n : ℤ) : (BrutalFiltrationQuotient.quotient R A p).X n ⟶ (BrutalFiltration.complex R A ((p + 1 : ℤ) : EInt)).X n :=
  (BrutalFiltrationQuotient.splitting R A p n).s

@[reassoc]
theorem retraction_toComplex (n : ℤ) (hn : n ≠ -(p + 1)) :
    retraction R A p n ≫ (BrutalFiltration.toComplex R A (p : EInt)).f n =
      (BrutalFiltration.toComplex R A ((p + 1 : ℤ) : EInt)).f n := by
  have hz : (BrutalFiltrationQuotient.projection R A p).f n = 0 :=
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-(p + 1)) (A.X (-(p + 1))) n hn).eq_of_tgt _ _
  have hr : retraction R A p n ≫ (BrutalFiltrationQuotient.stageMap R A p).f n = 𝟙 _ := by
    have h : retraction R A p n ≫ (BrutalFiltrationQuotient.stageMap R A p).f n =
        𝟙 _ - (BrutalFiltrationQuotient.projection R A p).f n ≫ sectionMap R A p n := (BrutalFiltrationQuotient.splitting R A p n).r_f
    simpa only [hz, zero_comp, sub_zero] using h
  have hi : (BrutalFiltrationQuotient.stageMap R A p).f n ≫ (BrutalFiltration.toComplex R A ((p + 1 : ℤ) : EInt)).f n =
      (BrutalFiltration.toComplex R A (p : EInt)).f n := rfl
  rw [← hi, ← Category.assoc, hr, Category.id_comp]

@[reassoc]
theorem section_toComplex :
    sectionMap R A p (-(p + 1)) ≫ (BrutalFiltration.toComplex R A ((p + 1 : ℤ) : EInt)).f (-(p + 1)) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-(p + 1)) (A.X (-(p + 1)))).hom := by
  have hs : sectionMap R A p (-(p + 1)) ≫ (BrutalFiltrationQuotient.projection R A p).f (-(p + 1)) = 𝟙 _ :=
    (BrutalFiltrationQuotient.splitting R A p (-(p + 1))).s_g
  have hp : (BrutalFiltrationQuotient.projection R A p).f (-(p + 1)) =
      (BrutalFiltration.toComplex R A ((p + 1 : ℤ) : EInt)).f (-(p + 1)) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) (-(p + 1)) (A.X (-(p + 1)))).inv :=
    HomologicalComplex.mkHomToSingle_f _ _
  rw [hp] at hs
  rw [← cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) (-(p + 1)) (A.X (-(p + 1)))).inv,
    Category.assoc, hs, Iso.hom_inv_id]

@[reassoc]
theorem projection_toTerm :
    (BrutalFiltrationQuotient.projection R A p).f (-(p + 1)) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-(p + 1)) (A.X (-(p + 1)))).hom =
    (BrutalFiltration.toComplex R A ((p + 1 : ℤ) : EInt)).f (-(p + 1)) := by
  rw [BrutalFiltrationQuotient.projection, HomologicalComplex.mkHomToSingle_f, Category.assoc, Iso.inv_hom_id, Category.comp_id]

def boundaryCocycle : Cocycle (BrutalFiltrationQuotient.quotient R A (p + 1)) (BrutalFiltration.complex R A ((p + 1 : ℤ) : EInt)) 1 :=
  cocycleOfDegreewiseSplit (BrutalFiltrationQuotient.sequence R A (p + 1)) (BrutalFiltrationQuotient.splitting R A (p + 1))

def columnConnecting : Cocycle (BrutalFiltrationQuotient.quotient R A (p + 1)) (BrutalFiltrationQuotient.quotient R A p) 1 :=
  Cocycle.mk
    ((boundaryCocycle R A p).1.comp
      (Cochain.ofHom (BrutalFiltrationQuotient.projection R A p)) (add_zero 1)) 2 rfl (by
        rw [δ_comp_zero_cochain (boundaryCocycle R A p).1 (Cochain.ofHom (BrutalFiltrationQuotient.projection R A p)) 2 rfl]
        simp only [δ_ofHom, Cochain.comp_zero,
          Cocycle.δ_eq_zero, Cochain.zero_comp, add_zero])

theorem columnConnecting_value :
    (HomologicalComplex.singleObjXSelf (.up ℤ) (-((p + 1) + 1)) (A.X (-((p + 1) + 1)))).inv ≫
      (columnConnecting R A p).1.v (-((p + 1) + 1)) (-(p + 1)) (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-(p + 1)) (A.X (-(p + 1)))).hom =
    A.d (-((p + 1) + 1)) (-(p + 1)) := by
  simp only [columnConnecting, Cocycle.mk_coe, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, boundaryCocycle, cocycleOfDegreewiseSplit, Cochain.mk_v]
  change _ ≫ (sectionMap R A (p + 1) (-((p + 1) + 1)) ≫
    (BrutalFiltration.complex R A (((p + 1) + 1 : ℤ) : EInt)).d (-((p + 1) + 1)) (-(p + 1)) ≫
      retraction R A (p + 1) (-(p + 1))) ≫ (BrutalFiltrationQuotient.projection R A p).f (-(p + 1)) ≫ _ = _
  simp only [Category.assoc]
  rw [projection_toTerm, retraction_toComplex R A (p + 1) (-(p + 1)) (by omega),
    ← (BrutalFiltration.toComplex R A (((p + 1) + 1 : ℤ) : EInt)).comm,
    section_toComplex_assoc, Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalConnectingMap

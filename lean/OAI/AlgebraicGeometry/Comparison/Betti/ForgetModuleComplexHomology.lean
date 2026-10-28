import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Forget Module Complex Homology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ForgetModuleComplexHomology.Cech

noncomputable section

/-! Forgetting scalars preserves the original cycle and homology projections of a module complex. -/

open _root_.CategoryTheory

variable (R : Type) [Ring R] (K : CochainComplex (ModuleCat R) ℕ) (q : ℕ)

def moduleForgetComplexCyclesIso :
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).cycles q ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj (K.cycles q) :=
  (K.sc q).mapCyclesIso (forget₂ (ModuleCat R) AddCommGrpCat)

def moduleForgetComplexHomologyIso :
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).homology q ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj (K.homology q) :=
  ((K.sc q).map (forget₂ (ModuleCat R) AddCommGrpCat)).leftHomologyIso.symm ≪≫
    (K.sc q).mapLeftHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat) ≪≫
      (forget₂ (ModuleCat R) AddCommGrpCat).mapIso (K.sc q).leftHomologyIso

theorem moduleForgetComplexCyclesIso_hom_i :
    (moduleForgetComplexCyclesIso R K q).hom ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map (K.iCycles q) =
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).iCycles q :=
  (K.sc q).mapCyclesIso_hom_iCycles (forget₂ (ModuleCat R) AddCommGrpCat)

theorem moduleForgetComplexHomologyIso_homologyπ :
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).homologyπ q ≫
      (moduleForgetComplexHomologyIso R K q).hom =
    (moduleForgetComplexCyclesIso R K q).hom ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map (K.homologyπ q) := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let S := K.sc q
  have h : (S.map F).leftHomologyπ ≫ (S.mapLeftHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.leftHomologyπ :=
    (S.leftHomologyData.map F).leftHomologyπ_comp_leftHomologyIso_hom
  change (S.map F).homologyπ ≫
    ((S.map F).leftHomologyIso.inv ≫ (S.mapLeftHomologyIso F).hom ≫ F.map S.leftHomologyIso.hom) =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [← Category.assoc, ShortComplex.homologyπ_comp_leftHomologyIso_inv,
    ← Category.assoc, h, Category.assoc, ← F.map_comp]
  rfl

theorem moduleForgetComplexCyclesIso_inv_i :
    (moduleForgetComplexCyclesIso R K q).inv ≫
      (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).iCycles q =
    (forget₂ (ModuleCat R) AddCommGrpCat).map (K.iCycles q) := by
  rw [← moduleForgetComplexCyclesIso_hom_i]
  exact Iso.inv_hom_id_assoc (moduleForgetComplexCyclesIso R K q) _

theorem moduleForgetComplexHomologyIso_inv_homologyπ :
    (forget₂ (ModuleCat R) AddCommGrpCat).map (K.homologyπ q) ≫
      (moduleForgetComplexHomologyIso R K q).inv =
    (moduleForgetComplexCyclesIso R K q).inv ≫
      (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).homologyπ q := by
  rw [← cancel_epi (moduleForgetComplexCyclesIso R K q).hom, ← Category.assoc,
    ← moduleForgetComplexHomologyIso_homologyπ, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ForgetModuleComplexHomology.Cech

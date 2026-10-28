import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianFiberComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Staged Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.StagedRecovery.Construction

noncomputable section

section

/-! Enlarging a field of definition preserves the original abelian
recovery and its exact total map back to the first model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

variable {S T Y : Scheme.{0}} {g : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y)
    (v : T ⟶ S) (u : Y ⟶ T) (w : Y ⟶ S) (hu : u ≫ v = w)
    (e : A.scheme ≅ (B.pullback w).scheme)

def stagedAbelianRecovery : A.scheme ≅ ((B.pullback v).pullback u).scheme :=
  e ≪≫ (PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso B.scheme v u w hu).symm

instance stagedAbelianRecovery_isMonHom [IsMonHom e.hom] :
    IsMonHom (stagedAbelianRecovery B A v u w hu e).hom := by
  let t := PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso B.scheme v u w hu
  have ht : IsMonHom t.hom := PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom B.scheme v u w hu
  have hi : IsMonHom t.inv := inferInstance
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ ‹IsMonHom e.hom› hi

set_option backward.isDefEq.respectTransparency false in
theorem stagedAbelianRecovery_totalMap_comp :
    AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A.scheme (B.pullback v).scheme
      (stagedAbelianRecovery B A v u w hu e) ≫ pullback.fst B.scheme.hom v =
        AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap w A.scheme B.scheme e := by
  let t := PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso B.scheme v u w hu
  have ht : t.hom.left ≫ pullback.fst B.scheme.hom w =
      pullback.fst (pullback.snd B.scheme.hom v) u ≫ pullback.fst B.scheme.hom v :=
    PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst B.scheme v u w hu
  have hi : t.inv.left ≫ pullback.fst (pullback.snd B.scheme.hom v) u ≫
      pullback.fst B.scheme.hom v = pullback.fst B.scheme.hom w := by
    rw [← ht, ← Category.assoc]
    have he : t.inv.left ≫ t.hom.left = 𝟙 _ := congrArg Over.Hom.left t.inv_hom_id
    rw [he, Category.id_comp]
  change ((e.hom.left ≫ t.inv.left) ≫ pullback.fst (pullback.snd B.scheme.hom v) u) ≫
      pullback.fst B.scheme.hom v = e.hom.left ≫ pullback.fst B.scheme.hom w
  rw [Category.assoc, Category.assoc, hi]

end

/-! An actual line on a recovered abelian variety has the same
parameter restriction after an enlargement of its field of definition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

def recoveredFamilyParameterIso {S Y : Scheme.{0}} (u : Y ⟶ S)
    (B : Over S) {A : Over Y} (e : A ≅ (Over.pullback u).obj B) :
    A.left ≅ (Over.mk u ⊗ B).left :=
  (Over.forget Y).mapIso e ≪≫ pullbackSymmetry B.hom u

theorem recoveredFamilyParameterIso_fst {S Y : Scheme.{0}} (u : Y ⟶ S)
    (B : Over S) {A : Over Y} (e : A ≅ (Over.pullback u).obj B) :
    (recoveredFamilyParameterIso u B e).hom ≫ (fst (Over.mk u) B).left = A.hom := by
  change (e.hom.left ≫ (pullbackSymmetry B.hom u).hom) ≫ pullback.fst u B.hom = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact e.hom.w

theorem recoveredFamilyParameterIso_snd {S Y : Scheme.{0}} (u : Y ⟶ S)
    (B : Over S) {A : Over Y} (e : A ≅ (Over.pullback u).obj B) :
    (recoveredFamilyParameterIso u B e).hom ≫ (snd (Over.mk u) B).left =
      AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A B e := by
  change (e.hom.left ≫ (pullbackSymmetry B.hom u).hom) ≫ pullback.snd u B.hom = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem stagedLineRecovery_square
    {S T Y : Scheme.{0}} {g : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y)
    (v : T ⟶ S) (u : Y ⟶ T) (w : Y ⟶ S) (hu : u ≫ v = w)
    (e : A.scheme ≅ (B.pullback w).scheme) :
    AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A.scheme (B.pullback v).scheme
        (stagedAbelianRecovery B A v u w hu e) ≫ (pullbackSymmetry B.scheme.hom v).hom =
      (recoveredFamilyParameterIso w B.scheme e).hom ≫
        ((Over.homMk u hu : Over.mk w ⟶ Over.mk v) ▷ B.scheme).left := by
  let q : Over.mk w ⟶ Over.mk v := Over.homMk u hu
  let e₀ : A.scheme ≅ (Over.pullback w).obj B.scheme := e
  let e' : A.scheme ≅ (Over.pullback u).obj ((Over.pullback v).obj B.scheme) :=
    stagedAbelianRecovery B A v u w hu e
  let m : A.scheme.left ⟶ pullback B.scheme.hom v :=
    AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A.scheme ((Over.pullback v).obj B.scheme) e'
  let c := recoveredFamilyParameterIso w B.scheme e₀
  change m ≫ (pullbackSymmetry B.scheme.hom v).hom = c.hom ≫ (q ▷ B.scheme).left
  apply pullback.hom_ext
  · change (m ≫ (pullbackSymmetry B.scheme.hom v).hom) ≫ (fst (Over.mk v) B.scheme).left =
      (c.hom ≫ (q ▷ B.scheme).left) ≫ (fst (Over.mk v) B.scheme).left
    have hq : (q ▷ B.scheme).left ≫ (fst (Over.mk v) B.scheme).left =
        (fst (Over.mk w) B.scheme).left ≫ u := Over.whiskerRight_left_fst q
    rw [Category.assoc, Category.assoc, hq,
      ← Category.assoc c.hom (fst (Over.mk w) B.scheme).left u, recoveredFamilyParameterIso_fst]
    change m ≫ (pullbackSymmetry B.scheme.hom v).hom ≫ pullback.fst v B.scheme.hom = _
    rw [pullbackSymmetry_hom_comp_fst]
    exact AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap_base u A.scheme (B.pullback v).scheme e'
  · change (m ≫ (pullbackSymmetry B.scheme.hom v).hom) ≫ (snd (Over.mk v) B.scheme).left =
      (c.hom ≫ (q ▷ B.scheme).left) ≫ (snd (Over.mk v) B.scheme).left
    have hq : (q ▷ B.scheme).left ≫ (snd (Over.mk v) B.scheme).left =
        (snd (Over.mk w) B.scheme).left := Over.whiskerRight_left_snd q
    rw [Category.assoc, Category.assoc, hq, recoveredFamilyParameterIso_snd]
    change m ≫ (pullbackSymmetry B.scheme.hom v).hom ≫ pullback.snd v B.scheme.hom = _
    rw [pullbackSymmetry_hom_comp_snd]
    exact stagedAbelianRecovery_totalMap_comp B A v u w hu e

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.StagedRecovery.Construction

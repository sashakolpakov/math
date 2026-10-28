import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FieldSpecialization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso

/-! # Field Fiber Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Vanishing on every actual field fiber of the Poincare family away from the dual identity. The comparison is the unique isomorphism between the two Cartesian squares. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {K : Type u} [Field K] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A) (c : Spec (.of K) ⟶ S)
variable (x : (Over.map c).obj (𝟙_ (Over (Spec (.of K)))) ⟶ D.abelian.scheme)
variable {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left}
variable {b : P ⟶ Spec (.of K)}
variable (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) x.left)

def Dual.Data.DualAbelianData.poincareFieldFiberIso : (A.pullback c).scheme.left ≅ P :=
  (D.poincareFieldSpecialization_isPullback c x).isoPullback ≪≫ H.isoPullback.symm

theorem Dual.Data.DualAbelianData.poincareFieldFiberIso_hom_map :
    (D.poincareFieldFiberIso c x H).hom ≫ a = D.poincareFieldSpecializationMap c x := by
  change ((D.poincareFieldSpecialization_isPullback c x).isoPullback.hom ≫ H.isoPullback.inv) ≫ a = _
  rw [Category.assoc, H.isoPullback_inv_fst,
    (D.poincareFieldSpecialization_isPullback c x).isoPullback_hom_fst]

theorem Dual.Data.DualAbelianData.poincareFieldFiberIso_hom_base :
    (D.poincareFieldFiberIso c x H).hom ≫ b = (A.pullback c).scheme.hom := by
  change ((D.poincareFieldSpecialization_isPullback c x).isoPullback.hom ≫ H.isoPullback.inv) ≫ b = _
  rw [Category.assoc, H.isoPullback_inv_snd,
    (D.poincareFieldSpecialization_isPullback c x).isoPullback_hom_snd]

include H in
theorem Dual.Data.DualAbelianData.poincareFieldFiber_cohomology_vanish (hx : x ≠ 1) (n : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (D.poincare.pullback a).sheaf n) := by
  have hA : IsProper A.scheme.hom := A.proper
  have hfst : IsProper (pullback.fst D.abelian.scheme.hom A.scheme.hom) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hA
  have : IsProper b := MorphismProperty.of_isPullback (P := @IsProper) H hfst
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  let e := D.poincareFieldFiberIso c x H
  let L := D.poincare.pullback a
  let eL : (L.pullback e.hom).sheaf ≅
      (D.poincare.pullback (D.poincareFieldSpecializationMap c x)).sheaf :=
    (Scheme.Modules.pullbackComp e.hom a).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (D.poincareFieldFiberIso_hom_map c x H)).app D.poincare.sheaf
  have hzero := D.poincareFieldSpecialization_cohomology_vanish c x hx n
  let eC := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.pullback c).scheme.left n).mapIso eL
  have hi : Function.Injective eC.hom :=
    (AddCommGrpCat.mono_iff_injective eC.hom).mp inferInstance
  have hs : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback e.hom).sheaf n) :=
    ⟨fun v w => hi (hzero.elim _ _)⟩
  let h := CohomologyPullbackIso.lineBundleCohomologyPullbackIso e.hom b L n
  have hj : Function.Injective h.inv :=
    (ModuleCat.mono_iff_injective h.inv).mp inferInstance
  exact ⟨fun v w => hj (hs.elim _ _)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

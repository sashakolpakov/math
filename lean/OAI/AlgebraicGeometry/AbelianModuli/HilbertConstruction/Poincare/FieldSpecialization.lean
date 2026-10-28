import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PoincarePointCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback

/-! # Field Specialization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A field-valued point of the dual over an arbitrary base gives the actual Cartesian fiber of the Poincare family. Away from the identity, this fiber has zero cohomology in every degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {K : Type u} [Field K] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A) (c : Spec (.of K) ⟶ S)
variable (x : (Over.map c).obj (𝟙_ (Over (Spec (.of K)))) ⟶ D.abelian.scheme)

theorem Dual.Data.DualAbelianData.fieldDualPoint_ne_one_of_point_outside_zero (k : Spec (.of K))
    (hx : x.left k ∉ Set.range η[D.abelian.scheme].left) : x ≠ 1 := by
  intro h
  apply hx
  rw [h, Hom.one_def]
  exact ⟨(toUnit ((Over.map c).obj (𝟙_ (Over (Spec (.of K)))))).left k, rfl⟩

def Dual.Data.DualAbelianData.poincareFieldSpecializationPoint :
    𝟙_ (Over (Spec (.of K))) ⟶ (D.abelian.pullback c).scheme :=
  (D.abelian.baseChangePointsMulEquiv c (𝟙_ (Over (Spec (.of K))))).symm x

theorem Dual.Data.DualAbelianData.poincareFieldSpecializationPoint_ne_one (hx : x ≠ 1) :
    D.poincareFieldSpecializationPoint c x ≠ 1 := by
  intro h
  apply hx
  have he := congrArg (D.abelian.baseChangePointsMulEquiv c (𝟙_ (Over (Spec (.of K))))) h
  simpa only [Dual.Data.DualAbelianData.poincareFieldSpecializationPoint, MulEquiv.apply_symm_apply, map_one] using he

def Dual.Data.DualAbelianData.poincareFieldSpecializationMap :
    (A.pullback c).scheme.left ⟶ (D.abelian.scheme ⊗ A.scheme).left :=
  (lift ((Over.map c).map (toUnit (A.pullback c).scheme) ≫ x)
    (Dual.Data.DualAbelianData.baseChangeProjection A c)).left

theorem Dual.Data.DualAbelianData.poincareFieldSpecializationMap_fst :
    D.poincareFieldSpecializationMap c x ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
      (A.pullback c).scheme.hom ≫ x.left := by
  exact congrArg Over.Hom.left (lift_fst
    ((Over.map c).map (toUnit (A.pullback c).scheme) ≫ x) (Dual.Data.DualAbelianData.baseChangeProjection A c))

theorem Dual.Data.DualAbelianData.poincareFieldSpecializationMap_snd :
    D.poincareFieldSpecializationMap c x ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
      pullback.fst A.scheme.hom c := by
  have h := congrArg Over.Hom.left (lift_snd
    ((Over.map c).map (toUnit (A.pullback c).scheme) ≫ x) (Dual.Data.DualAbelianData.baseChangeProjection A c))
  change D.poincareFieldSpecializationMap c x ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
    (𝟙 (A.pullback c).scheme.left) ≫ pullback.fst A.scheme.hom c at h
  exact h.trans (Category.id_comp _)

theorem Dual.Data.DualAbelianData.poincareFieldSpecialization_isPullback :
    IsPullback (D.poincareFieldSpecializationMap c x) (A.pullback c).scheme.hom
      (pullback.fst D.abelian.scheme.hom A.scheme.hom) x.left := by
  have hx : x.left ≫ D.abelian.scheme.hom = c := x.w.trans (Category.id_comp c)
  have hr : IsPullback
      (D.poincareFieldSpecializationMap c x ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom)
      (A.pullback c).scheme.hom A.scheme.hom (x.left ≫ D.abelian.scheme.hom) := by
    rw [D.poincareFieldSpecializationMap_snd, hx]
    exact IsPullback.of_hasPullback A.scheme.hom c
  exact IsPullback.of_right hr (D.poincareFieldSpecializationMap_fst c x)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip

def Dual.Data.DualAbelianData.poincareFieldSpecializationBundleIso :
    ((D.pullback c).poincarePointBundle (D.poincareFieldSpecializationPoint c x)).sheaf ≅
      (D.poincare.pullback (D.poincareFieldSpecializationMap c x)).sheaf := by
  let B := (A.pullback c).scheme
  let z := D.poincareFieldSpecializationPoint c x
  have hz : D.abelian.baseChangePointsEquiv c (𝟙_ (Over (Spec (.of K)))) z = x :=
    (D.abelian.baseChangePointsMulEquiv c (𝟙_ (Over (Spec (.of K))))).apply_symm_apply x
  have h : D.abelian.baseChangePointsEquiv c B (toUnit B ≫ z) =
      (Over.map c).map (toUnit B) ≫ x := by
    rw [Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp, hz]
  let e := D.poincarePair_baseChangeIso c (toUnit B ≫ z) (𝟙 B)
  change ((D.pullback c).poincarePointBundle z).sheaf ≅
    (D.poincarePair (D.abelian.baseChangePointsEquiv c B (toUnit B ≫ z))
      (Dual.Data.DualAbelianData.baseChangeProjection A c)).sheaf at e
  rw [h] at e
  exact e ≪≫ D.poincarePairDirectIso ((Over.map c).map (toUnit B) ≫ x) (Dual.Data.DualAbelianData.baseChangeProjection A c)

theorem Dual.Data.DualAbelianData.poincareFieldSpecialization_cohomology_vanish (hx : x ≠ 1) (n : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      (D.poincare.pullback (D.poincareFieldSpecializationMap c x)).sheaf n) := by
  have hz := (D.pullback c).poincarePointBundle_cohomology_vanish_overField
    (D.poincareFieldSpecializationPoint c x) (D.poincareFieldSpecializationPoint_ne_one c x hx) n
  let e := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.pullback c).scheme.left n).mapIso
    (D.poincareFieldSpecializationBundleIso c x)
  have hi : Function.Injective e.inv :=
    (AddCommGrpCat.mono_iff_injective e.inv).mp inferInstance
  exact ⟨fun a b => hi (hz.elim _ _)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

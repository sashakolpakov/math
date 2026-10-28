import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingDerivedCocycle
import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-! # Connecting Resolution Cocycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingResolutionCocycle

noncomputable section

/-! Construct the actual cocycle representing a short exact sequence in an injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {S : ShortComplex C} (hS : S.ShortExact) (R : InjectiveResolution S.X₁)

def connectingResolutionMiddle : S.X₂ ⟶ R.cocomplex.X 0 := by
  have := hS.mono_f
  exact Injective.factorThru (R.ι.f 0) S.f

theorem connectingResolutionMiddle_comm : S.f ≫ connectingResolutionMiddle hS R = R.ι.f 0 := by
  have := hS.mono_f
  exact Injective.comp_factorThru _ _

def connectingResolutionQuotient : S.X₃ ⟶ R.cocomplex.X 1 := by
  have := hS.epi_g
  exact hS.exact.desc (connectingResolutionMiddle hS R ≫ R.cocomplex.d 0 1) (by
    rw [← Category.assoc, connectingResolutionMiddle_comm]
    exact R.ι_f_zero_comp_complex_d)

theorem connectingResolutionQuotient_comm : S.g ≫ connectingResolutionQuotient hS R =
    connectingResolutionMiddle hS R ≫ R.cocomplex.d 0 1 := by
  have := hS.epi_g
  exact hS.exact.g_desc _ _

theorem connectingResolutionQuotient_closed :
    connectingResolutionQuotient hS R ≫ R.cocomplex.d 1 2 = 0 := by
  have := hS.epi_g
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, connectingResolutionQuotient_comm, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero, comp_zero]

def connectingResolutionCochain :
    Cochain ((singleFunctor C 0).obj S.X₂) R.cochainComplex 0 :=
  Cochain.fromSingleMk (connectingResolutionMiddle hS R ≫ (R.cochainComplexXIso 0 0 rfl).inv)
    (zero_add 0)

def connectingResolutionCocycle :
    Cocycle ((singleFunctor C 0).obj S.X₃) R.cochainComplex 1 :=
  Cocycle.fromSingleMk (connectingResolutionQuotient hS R ≫ (R.cochainComplexXIso 1 1 rfl).inv)
    (zero_add 1) 2 rfl (by
      rw [R.cochainComplex_d 1 2 1 2 rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, connectingResolutionQuotient_closed, zero_comp])

theorem resolutionAugmentation_fromSingle :
    Cochain.fromSingleMk (X := S.X₁) (R.ι.f 0 ≫ (R.cochainComplexXIso 0 0 rfl).inv) (zero_add 0) =
      Cochain.ofHom R.ι' := by
  ext p
  by_cases hp : p = 0
  · subst p
    rw [Cochain.fromSingleMk_v, Cochain.ofHom_v, R.ι'_f_zero]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₁ p hp).eq_of_src _ _

theorem connectingResolutionCochain_lift :
    (Cochain.ofHom ((singleFunctor C 0).map S.f)).comp
      (connectingResolutionCochain hS R) (zero_add 0) = Cochain.ofHom R.ι' := by
  unfold connectingResolutionCochain
  rw [← Cochain.fromSingleMk_precomp, ← Category.assoc, connectingResolutionMiddle_comm]
  exact resolutionAugmentation_fromSingle R

theorem connectingResolutionCochain_d :
    δ 0 1 (connectingResolutionCochain hS R) =
      (Cochain.ofHom ((singleFunctor C 0).map S.g)).comp
        (connectingResolutionCocycle hS R).val (zero_add 1) := by
  unfold connectingResolutionCochain connectingResolutionCocycle
  rw [Cochain.δ_fromSingleMk _ _ 1 1 (zero_add 1), Cocycle.fromSingleMk_coe,
    ← Cochain.fromSingleMk_precomp]
  congr 1
  rw [R.cochainComplex_d 0 1 0 1 rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← connectingResolutionQuotient_comm, Category.assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingResolutionCocycle

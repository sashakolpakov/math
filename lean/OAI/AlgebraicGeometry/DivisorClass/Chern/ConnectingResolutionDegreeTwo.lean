import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingDerivedDegreeTwo
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingResolutionCocycle

/-! # Connecting Resolution Degree Two -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingResolutionDegreeTwo

noncomputable section

/-! Construct the actual resolution cocycle for the product with a short exact sequence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {S : ShortComplex C} (hS : S.ShortExact) {Y : C} (R : InjectiveResolution Y)
  (f : S.X₁ ⟶ R.cocomplex.X 1) (hf : f ≫ R.cocomplex.d 1 2 = 0)

def connectingResolutionOneMiddle : S.X₂ ⟶ R.cocomplex.X 1 := by
  have := hS.mono_f
  exact Injective.factorThru f S.f

theorem connectingResolutionOneMiddle_comm : S.f ≫ connectingResolutionOneMiddle hS R f = f := by
  have := hS.mono_f
  exact Injective.comp_factorThru _ _

def connectingResolutionTwoQuotient : S.X₃ ⟶ R.cocomplex.X 2 := by
  have := hS.epi_g
  exact hS.exact.desc (connectingResolutionOneMiddle hS R f ≫ R.cocomplex.d 1 2) (by
    rw [← Category.assoc, connectingResolutionOneMiddle_comm, hf])

theorem connectingResolutionTwoQuotient_comm :
    S.g ≫ connectingResolutionTwoQuotient hS R f hf =
      connectingResolutionOneMiddle hS R f ≫ R.cocomplex.d 1 2 := by
  have := hS.epi_g
  exact hS.exact.g_desc _ _

theorem connectingResolutionTwoQuotient_closed :
    connectingResolutionTwoQuotient hS R f hf ≫ R.cocomplex.d 2 3 = 0 := by
  have := hS.epi_g
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, connectingResolutionTwoQuotient_comm, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero, comp_zero]

def resolutionOneCocycle : Cocycle ((singleFunctor C 0).obj S.X₁) R.cochainComplex 1 :=
  Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso 1 1 rfl).inv) (zero_add 1) 2 rfl (by
    rw [R.cochainComplex_d 1 2 1 2 rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])

def connectingResolutionOneCochain : Cochain ((singleFunctor C 0).obj S.X₂) R.cochainComplex 1 :=
  Cochain.fromSingleMk (connectingResolutionOneMiddle hS R f ≫ (R.cochainComplexXIso 1 1 rfl).inv)
    (zero_add 1)

def connectingResolutionTwoCocycle : Cocycle ((singleFunctor C 0).obj S.X₃) R.cochainComplex 2 :=
  Cocycle.fromSingleMk (connectingResolutionTwoQuotient hS R f hf ≫ (R.cochainComplexXIso 2 2 rfl).inv)
    (zero_add 2) 3 rfl (by
      rw [R.cochainComplex_d 2 3 2 3 rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, connectingResolutionTwoQuotient_closed, zero_comp])

theorem connectingResolutionOneCochain_lift :
    (Cochain.ofHom ((singleFunctor C 0).map S.f)).comp
      (connectingResolutionOneCochain hS R f) (zero_add 1) = (resolutionOneCocycle R f hf).val := by
  unfold connectingResolutionOneCochain resolutionOneCocycle
  rw [Cocycle.fromSingleMk_coe, ← Cochain.fromSingleMk_precomp,
    ← Category.assoc, connectingResolutionOneMiddle_comm]

theorem connectingResolutionOneCochain_d :
    δ 1 2 (connectingResolutionOneCochain hS R f) =
      (Cochain.ofHom ((singleFunctor C 0).map S.g)).comp
        (connectingResolutionTwoCocycle hS R f hf).val (zero_add 2) := by
  unfold connectingResolutionOneCochain connectingResolutionTwoCocycle
  rw [Cochain.δ_fromSingleMk _ _ 2 2 (zero_add 2), Cocycle.fromSingleMk_coe,
    ← Cochain.fromSingleMk_precomp]
  congr 1
  rw [R.cochainComplex_d 1 2 1 2 rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← connectingResolutionTwoQuotient_comm, Category.assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingResolutionDegreeTwo

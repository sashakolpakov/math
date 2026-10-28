import OAI.NumberTheory.PadicHodge.PeriodInvariants.MappingConeQuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Regular Element Koszul -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RegularElementKoszul

noncomputable section

/-! Adjoining a regular element to a module resolution by its actual scalar
multiplication mapping cone. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

abbrev single := HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0

def scalar (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : R) : K ⟶ K where
  f n := ModuleCat.ofHom (r • LinearMap.id)
  comm' i j _ := by
    ext x
    exact (K.d i j).hom.map_smul r x

theorem scalar_naturality {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (r : R) : scalar K r ≫ f = f ≫ scalar L r := by
  ext n x
  exact (f.f n).hom.map_smul r x

theorem scalar_single (M : ModuleCat.{u} R) (r : R) :
    scalar (RegularElementKoszul.single.obj M) r = RegularElementKoszul.single.map (ModuleCat.ofHom (r • (LinearMap.id : M →ₗ[R] M))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _

def sequence (M : ModuleCat.{u} R) (r : R) : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (r • (LinearMap.id : M →ₗ[R] M))
    (Submodule.mkQ (r • (⊤ : Submodule R M))) (by
      ext x
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.smul_mem_pointwise_smul x r ⊤ trivial)

theorem sequence_shortExact (M : ModuleCat.{u} R) (r : R) (hr : IsSMulRegular M r) :
    (sequence M r).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change Submodule.Quotient.mk x = (0 : QuotSMulTop r M) ↔
      ∃ y : M, r • y = x
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and]
    rfl
  · exact hr
  · exact Submodule.mkQ_surjective _

def quotientAugmentation (M : ModuleCat.{u} R) (r : R) :
    CochainComplex.mappingCone (scalar (RegularElementKoszul.single.obj M) r) ⟶
      RegularElementKoszul.single.obj (ModuleCat.of R (QuotSMulTop r M)) :=
  eqToHom (by rw [scalar_single]; rfl) ≫
    CochainComplex.mappingCone.descShortComplex ((sequence M r).map RegularElementKoszul.single)

theorem quotientAugmentation_quasiIso (M : ModuleCat.{u} R) (r : R)
    (hr : IsSMulRegular M r) : QuasiIso (quotientAugmentation M r) := by
  have hq : QuasiIso (CochainComplex.mappingCone.descShortComplex ((sequence M r).map RegularElementKoszul.single)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
    ((sequence_shortExact M r hr).map_of_exact RegularElementKoszul.single)
  unfold quotientAugmentation
  exact quasiIso_comp _ _

def stepAugmentation {K : CochainComplex (ModuleCat.{u} R) ℤ} (M : ModuleCat.{u} R)
    (ε : K ⟶ RegularElementKoszul.single.obj M) (r : R) :
    CochainComplex.mappingCone (scalar K r) ⟶
      RegularElementKoszul.single.obj (ModuleCat.of R (QuotSMulTop r M)) :=
  CochainComplex.mappingCone.map _ _ ε ε (scalar_naturality ε r) ≫
    quotientAugmentation M r

theorem stepAugmentation_quasiIso {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (M : ModuleCat.{u} R) (ε : K ⟶ RegularElementKoszul.single.obj M) (hε : QuasiIso ε)
    (r : R) (hr : IsSMulRegular M r) : QuasiIso (stepAugmentation M ε r) := by
  have := PeriodInvariants.MappingConeQuasiIso.quasiIso_map (scalar K r) (scalar (RegularElementKoszul.single.obj M) r)
    ε ε (scalar_naturality ε r) hε hε
  have := quotientAugmentation_quasiIso M r hr
  exact quasiIso_comp _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RegularElementKoszul

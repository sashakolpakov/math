import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeHeisenberg
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier

/-! # Prime Test Operators -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization

noncomputable section

/-! Full-prime tensor inputs and Heisenberg operators on the actual test spaces. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q n : ℕ) [Fact q.Prime]

def fullPrimeTensor (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) :=
  FiniteLocalOperators.Realization.finiteProductTestEquiv (PrimeChart.Realization.fullPrimeChart q) (TensorCommutant.Realization.tensorTest ((FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm f) h)

theorem fullPrimeTensor_apply (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) (x : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (fullPrimeTensor q n f h).val x = f.val (PrimeChart.Realization.fullPrimeProjection q x) * h.val (PrimeChart.Realization.fullPrimeAway q x) := by
  exact TensorCommutant.Realization.tensorTest_apply ((FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm f) h
    (PrimeChart.Realization.fullPrimeProjection q x) (PrimeChart.Realization.fullPrimeAway q x)

theorem fullPrimeTensor_linear_ext (U V : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n))
    (h : ∀ f k, U (fullPrimeTensor q n f k) = V (fullPrimeTensor q n f k)) : U = V := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (PrimeChart.Realization.fullPrimeChart q (ι := Fin n))
  have heq : U.comp E.toLinearMap = V.comp E.toLinearMap := by
    apply TensorCommutant.Realization.test_linear_ext
    intro f k
    have hf := h (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n f) k
    change U (E (TensorCommutant.Realization.tensorTest ((FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm
      (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n f)) k)) = _ at hf
    rw [LinearEquiv.symm_apply_apply] at hf
    exact hf
  apply LinearMap.ext
  intro f
  obtain ⟨a, rfl⟩ := E.surjective f
  exact LinearMap.congr_fun heq a

def fullPrimeOperatorHom :
    (Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) →*
      (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :=
  (TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.finiteProductTestEquiv (PrimeChart.Realization.fullPrimeChart q))).comp
    (TensorCommutant.Realization.extendTestHom.comp (TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm))

theorem fullPrimeOperatorHom_tensor (U : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) :
    fullPrimeOperatorHom q n U (fullPrimeTensor q n f h) = fullPrimeTensor q n (U f) h := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (PrimeChart.Realization.fullPrimeChart q (ι := Fin n))
  let L := FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n
  change E (TensorCommutant.Realization.extendTestHom (TensorCommutant.Realization.conjugateLinearAut L.symm U)
    (E.symm (E (TensorCommutant.Realization.tensorTest (L.symm f) h)))) = E (TensorCommutant.Realization.tensorTest (L.symm (U f)) h)
  rw [E.symm_apply_apply, TensorCommutant.Realization.extendTestHom_tensor]
  change E (TensorCommutant.Realization.tensorTest (L.symm (U (L (L.symm f)))) h) = E (TensorCommutant.Realization.tensorTest (L.symm (U f)) h)
  rw [L.apply_symm_apply]

theorem fullPrimeOperatorHom_neg : fullPrimeOperatorHom q n (LinearEquiv.neg ℂ) = LinearEquiv.neg ℂ := by
  unfold fullPrimeOperatorHom
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, TensorCommutant.Realization.conjugateLinearAut_neg,
    TensorCommutant.Realization.extendTestHom_neg, TensorCommutant.Realization.conjugateLinearAut_neg]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem awayHeisenberg_mem (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Fin n) MpR MpF MpA)
    (p s : PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))
    (f : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) :
    PrimeHeisenberg.Realization.awayHeisenbergFunction q D p s f.val ∈ TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n)) := by
  constructor
  · apply IsLocallyConstant.mul
    · apply (FiniteSchur.Realization.finiteCharacter_locallyConstant D).comp_continuous
      unfold dotProduct
      fun_prop
    · exact f.property.1.comp_continuous (continuous_id.sub continuous_const)
  · exact (f.property.2.comp_homeomorph (Homeomorph.subRight s)).mul_left

def awayHeisenbergOperator (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Fin n) MpR MpF MpA)
    (p s : PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n)) :
    TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n)) →ₗ[ℂ]
      TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n)) where
  toFun f := ⟨PrimeHeisenberg.Realization.awayHeisenbergFunction q D p s f.val, awayHeisenberg_mem q n D p s f⟩
  map_add' f h := by
    apply Subtype.ext
    funext y
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext y
    exact mul_left_comm _ _ _

theorem fullPrime_heisenberg_tensor (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Fin n) MpR MpF MpA)
    (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (h : TestSections.Realization.lcCompactSpace (PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) :
    FiniteSchur.Realization.finiteHeisenbergOperator D p s (fullPrimeTensor q n f h) =
      fullPrimeTensor q n
        (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (FiniteSchur.Realization.finiteLocalCharacter q D)
          (FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
          (Sum.elim (PrimeChart.Realization.fullPrimeProjection q s) (PrimeChart.Realization.fullPrimeProjection q p)) f)
        (awayHeisenbergOperator q n D (PrimeChart.Realization.fullPrimeAway q p) (PrimeChart.Realization.fullPrimeAway q s) h) := by
  apply Subtype.ext
  funext x
  have hfun : (fullPrimeTensor q n f h).val =
      fun z => f.val (PrimeChart.Realization.fullPrimeProjection q z) * h.val (PrimeChart.Realization.fullPrimeAway q z) :=
    funext (fullPrimeTensor_apply q n f h)
  change Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p s (fullPrimeTensor q n f h).val x = _
  rw [hfun, PrimeHeisenberg.Realization.fullPrime_heisenberg_function, fullPrimeTensor_apply,
    PrimeHeisenberg.Realization.padic_heisenberg_coordinate_convention]
  rfl

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization

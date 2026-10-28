import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter
import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier

/-! # Local Test Commutant -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.LocalTestCommutant.CM

/-! The actual local Heisenberg commutant is scalar in every dimension.
Consequently its commutant on product tests commutes with every operator
on the local factor. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter.CM
variable (q n : ℕ) [Fact q.Prime]

def heisenberg (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) :
    RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) :=
  (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm.toLinearMap.comp
    ((RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_continuous q) v).toLinearMap.comp
      (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).toLinearMap)

theorem heisenberg_realization (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) (f : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n)) :
    RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n (heisenberg q n v f) =
      RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_continuous q) v
        (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n f) :=
  (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).apply_symm_apply _

theorem commutant_scalar
    (A : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n))
    (hA : ∀ v f, A (heisenberg q n v f) = heisenberg q n v (A f)) :
    ∃ c : ℂ, ∀ f, A f = c • f := by
  let L := RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n
  let B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n →ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n :=
    L.toLinearMap.comp (A.comp L.symm.toLinearMap)
  have hB (f : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n)) : B (L f) = L (A f) := by simp [B]
  have hcomm v f : B (RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_continuous q) v f) =
      RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_continuous q) v (B f) := by
    obtain ⟨f, rfl⟩ := L.surjective f
    calc
      _ = B (L (heisenberg q n v f)) := congrArg B (heisenberg_realization q n v f).symm
      _ = L (A (heisenberg q n v f)) := hB _
      _ = L (heisenberg q n v (A f)) := congrArg L (hA v f)
      _ = RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_continuous q) v (L (A f)) :=
        heisenberg_realization q n v (A f)
      _ = _ := congrArg (RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_continuous q) v) (hB f).symm
  obtain ⟨c, hc⟩ := RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction.ultra_commutant_scalar (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q)
    (PadicCharacter.CM.character q) (PadicCharacter.CM.character_continuous q) (PadicCharacter.CM.character_nontrivial q) (PadicCharacter.CM.character_unitary q) B hcomm
  refine ⟨c, ?_⟩
  intro f
  apply L.injective
  rw [map_smul]
  exact (hB f).symm.trans (hc (L f))

def vacuum : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) :=
  (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm
    (RepresentationTheory.Weil.UnitarySplitting.LocalTest.Construction.ultraTestVector ℚ_[q] (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) n)

theorem vacuum_zero : (vacuum q n).val 0 = 1 :=
  RepresentationTheory.Weil.UnitarySplitting.LocalTest.Construction.ultraTestVector_at_zero ℚ_[q] (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) n

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

theorem commutes_all_extended
    (U : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n × Y) →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n × Y))
    (hU : ∀ v f, U (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear (heisenberg q n v) f) = RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear (heisenberg q n v) (U f))
    (T : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n))
    (f : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n × Y)) :
    U (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear T f) = RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear T (U f) := by
  have he := RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.local_commutant_factors (heisenberg q n) (commutant_scalar q n) U hU
    (vacuum q n) 0 (vacuum_zero q n)
  have hmap : U.comp (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear T) = (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear T).comp U := by
    apply RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.test_linear_ext
    intro a b
    change U (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear T (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest a b)) = RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear T (U (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest a b))
    rw [he, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear_tensor, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestLinear_tensor, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestLinear_tensor, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear_tensor]
  exact LinearMap.congr_fun hmap f

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.LocalTestCommutant.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.LocalTestCommutant.CM.Prime

/-! A global test operator commuting with the Heisenberg action at one
prime commutes with every actual test operator at that prime. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicCharacter.CM
variable (q n : ℕ) [Fact q.Prime]

def localHeisenberg (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n :=
  RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator (PadicCharacter.CM.character q) (PadicCharacter.CM.character_continuous q) v

theorem operator_extension (T : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (f : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace ((Fin n → ℚ_[q]) × RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) :
    RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeChart q) f) =
      RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeChart q)
        (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear ((RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm T).toLinearMap) f) := by
  let E := RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeChart q (ι := Fin n))
  let L := RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n
  change E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestHom (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut L.symm T) (E.symm (E f))) = _
  rw [E.symm_apply_apply]
  rfl

theorem heisenberg_extension (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n)
    (f : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace ((Fin n → ℚ_[q]) × RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) :
    RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (localHeisenberg q n v) (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeChart q) f) =
      RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeChart q)
        (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear (heisenberg q n v) f) :=
  operator_extension q n (localHeisenberg q n v) f

theorem commutes_all_local
    (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n))
    (hU : ∀ v f, U (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (localHeisenberg q n v) f) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (localHeisenberg q n v) (U f))
    (T : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    U (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T f) = RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T (U f) := by
  let E := RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeChart q (ι := Fin n))
  let V := E.symm.toLinearMap.comp (U.comp E.toLinearMap)
  have hV : ∀ v a, V (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear (heisenberg q n v) a) =
      RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear (heisenberg q n v) (V a) := by
    intro v a
    apply E.injective
    change E (E.symm (U (E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear (heisenberg q n v) a)))) =
      E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear (heisenberg q n v) (E.symm (U (E a))))
    rw [E.apply_symm_apply, ← heisenberg_extension, ← heisenberg_extension, E.apply_symm_apply]
    exact hU v (E a)
  obtain ⟨a, rfl⟩ := E.surjective f
  rw [operator_extension]
  let R := (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] n).symm T).toLinearMap
  have h := congrArg E (commutes_all_extended q n V hV R a)
  change E (E.symm (U (E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear R a)))) =
    E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear R (E.symm (U (E a)))) at h
  rw [E.apply_symm_apply] at h
  calc
    _ = E (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.extendTestLinear R (E.symm (U (E a)))) := h
    _ = RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T (E (E.symm (U (E a)))) :=
      (operator_extension q n T (E.symm (U (E a)))).symm
    _ = _ := congrArg (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T) (E.apply_symm_apply (U (E a)))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.LocalTestCommutant.CM.Prime

end

end OAI

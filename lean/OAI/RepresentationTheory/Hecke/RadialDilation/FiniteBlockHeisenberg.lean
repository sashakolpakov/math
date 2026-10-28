import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
import OAI.RepresentationTheory.Hecke.RadialDilation.PadicTensorCommutant

/-! # Finite Block Heisenberg -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockHeisenberg.Realization

noncomputable section

/-! The actual finite Heisenberg action restricts to the chosen p-adic tensor factor. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} (μ : Place)

theorem finiteBlockChart_sub_fst (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) (s : Mem.Realization.Position q) :
    (FiniteBlockChart.Realization.finiteBlockChart q μ (x - FiniteBlockChart.Realization.finiteBlockInclusion q μ s)).1 =
      (FiniteBlockChart.Realization.finiteBlockChart q μ x).1 - s := by
  change FiniteBlockChart.Realization.finiteBlockProjection q μ (x - FiniteBlockChart.Realization.finiteBlockInclusion q μ s) = _
  rw [map_sub, FiniteBlockChart.Realization.finiteBlockProjection_inclusion]
  rfl

theorem finiteBlockChart_sub_snd (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) (s : Mem.Realization.Position q) :
    (FiniteBlockChart.Realization.finiteBlockChart q μ (x - FiniteBlockChart.Realization.finiteBlockInclusion q μ s)).2 =
      (FiniteBlockChart.Realization.finiteBlockChart q μ x).2 := by
  apply Subtype.ext
  change (x - FiniteBlockChart.Realization.finiteBlockInclusion q μ s) -
      FiniteBlockChart.Realization.finiteBlockInclusion q μ (FiniteBlockChart.Realization.finiteBlockProjection q μ (x - FiniteBlockChart.Realization.finiteBlockInclusion q μ s)) =
    x - FiniteBlockChart.Realization.finiteBlockInclusion q μ (FiniteBlockChart.Realization.finiteBlockProjection q μ x)
  rw [map_sub, FiniteBlockChart.Realization.finiteBlockProjection_inclusion, map_sub]
  abel

variable [Fintype Place]

theorem finiteBlock_heisenberg_phase (p s : Mem.Realization.Position q) (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (∑ j, FiniteBlockChart.Realization.finiteBlockInclusion q μ p j *
      (x j - algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * FiniteBlockChart.Realization.finiteBlockInclusion q μ s j)) =
    FiniteSchur.Realization.finitePadicInclusion q (∑ i, p i * (FiniteBlockChart.Realization.finiteBlockProjection q μ x i - s i / 2)) := by
  have h := FiniteBlockChart.Realization.finiteBlock_pairing q μ p (x - (1 / 2 : ℚ) • FiniteBlockChart.Realization.finiteBlockInclusion q μ s)
  have hleft : (∑ j, FiniteBlockChart.Realization.finiteBlockInclusion q μ p j *
      (x j - algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * FiniteBlockChart.Realization.finiteBlockInclusion q μ s j)) =
      ∑ j, FiniteBlockChart.Realization.finiteBlockInclusion q μ p j * (x - (1 / 2 : ℚ) • FiniteBlockChart.Realization.finiteBlockInclusion q μ s) j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def]
    rfl
  rw [hleft, h]
  apply congrArg (FiniteSchur.Realization.finitePadicInclusion q)
  rw [map_sub, map_smul, FiniteBlockChart.Realization.finiteBlockProjection_inclusion]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def]
  change p i * (FiniteBlockChart.Realization.finiteBlockProjection q μ x i - algebraMap ℚ ℚ_[q] (1 / 2) * s i) = _
  rw [map_div₀, map_one, map_ofNat]
  ring

variable [DecidableEq Place]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

theorem finiteBlock_heisenberg_function (p s : Mem.Realization.Position q)
    (f : Mem.Realization.Position q → ℂ) (g : FiniteBlockChart.Realization.FiniteAwayPosition q μ → ℂ) (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)
      (fun y => f (FiniteBlockChart.Realization.finiteBlockChart q μ y).1 * g (FiniteBlockChart.Realization.finiteBlockChart q μ y).2) x =
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (FiniteSchur.Realization.finiteLocalCharacter q D) (Sum.elim s p) f (FiniteBlockChart.Realization.finiteBlockChart q μ x).1 *
      g (FiniteBlockChart.Realization.finiteBlockChart q μ x).2 := by
  unfold Theta.PoissonAutomorphyNormalizationData.heisenberg
  rw [finiteBlock_heisenberg_phase]
  change FiniteSchur.Realization.finiteLocalCharacter q D (∑ i, p i * (FiniteBlockChart.Realization.finiteBlockProjection q μ x i - s i / 2)) *
    (f (FiniteBlockChart.Realization.finiteBlockChart q μ (x - FiniteBlockChart.Realization.finiteBlockInclusion q μ s)).1 *
      g (FiniteBlockChart.Realization.finiteBlockChart q μ (x - FiniteBlockChart.Realization.finiteBlockInclusion q μ s)).2) = _
  rw [finiteBlockChart_sub_fst, finiteBlockChart_sub_snd]
  change _ =
    (FiniteSchur.Realization.finiteLocalCharacter q D (∑ i, p i * (FiniteBlockChart.Realization.finiteBlockProjection q μ x i - s i / 2)) *
      f ((FiniteBlockChart.Realization.finiteBlockChart q μ x).1 - s)) * g (FiniteBlockChart.Realization.finiteBlockChart q μ x).2
  exact (mul_assoc _ _ _).symm

theorem finiteBlock_heisenberg_tensor (p s : Mem.Realization.Position q)
    (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q)) (g : TestSections.Realization.lcCompactSpace (FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
    FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)
      (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) (TensorCommutant.Realization.tensorTest f g)) =
    FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
      (TensorCommutant.Realization.tensorTest (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
        (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (Sum.elim s p) f) g) := by
  apply Subtype.ext
  funext x
  have h := finiteBlock_heisenberg_function q μ D p s f.val g.val x
  convert h using 1
  · change Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)
      (fun y => (TensorCommutant.Realization.tensorTest f g).val (FiniteBlockChart.Realization.finiteBlockChart q μ y)) x = _
    have hfg : (fun y => (TensorCommutant.Realization.tensorTest f g).val (FiniteBlockChart.Realization.finiteBlockChart q μ y)) =
        (fun y => f.val (FiniteBlockChart.Realization.finiteBlockChart q μ y).1 * g.val (FiniteBlockChart.Realization.finiteBlockChart q μ y).2) :=
      funext (fun y => TensorCommutant.Realization.tensorTest_apply f g _ _)
    rw [hfg]
  · change (TensorCommutant.Realization.tensorTest (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
        (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (Sum.elim s p) f) g).val
      (FiniteBlockChart.Realization.finiteBlockChart q μ x) = _
    rw [TensorCommutant.Realization.tensorTest_apply]
    rfl

theorem finiteBlock_heisenberg_operator (p s : Mem.Realization.Position q)
    (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
    FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)
      (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) f) =
    FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
      (TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
        (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (Sum.elim s p)) f) := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
  have heq : (FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)).comp
      E.toLinearMap = E.toLinearMap.comp
        (TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
          (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (Sum.elim s p))) := by
    apply TensorCommutant.Realization.test_linear_ext
    intro h g
    change FiniteSchur.Realization.finiteHeisenbergOperator D _ _ (E (TensorCommutant.Realization.tensorTest h g)) = E (TensorCommutant.Realization.extendTestLinear _ (TensorCommutant.Realization.tensorTest h g))
    rw [TensorCommutant.Realization.extendTestLinear_tensor]
    exact finiteBlock_heisenberg_tensor q μ D p s h g
  exact LinearMap.congr_fun heq f

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockHeisenberg.Realization

import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace

/-! # Finite Local Operators -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization

noncomputable section

/-! Local operators acting on actual finite-adelic test functions. -/

open scoped Classical

def nonarchTestSpaceEquiv (k : Type) [NormedField k] [TotallyDisconnectedSpace k] (n : ℕ) :
    TestSections.Realization.lcCompactSpace (Fin n → k) ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n where
  toFun f := ⟨f.val, Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem f.property.1 f.property.2⟩
  invFun f := ⟨f.val, Weil.Local.NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteTestSpaceEquiv (ι : Type*) [Fintype ι] :
    TestSections.Realization.lcCompactSpace (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι where
  toFun f := ⟨f.val, (Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff f.val).mpr f.property⟩
  invFun f := ⟨f.val, (Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff f.val).mp f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteProductTestEquiv {ι X Y : Type*} [Fintype ι] [TopologicalSpace X] [TopologicalSpace Y]
    (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ X × Y) : TestSections.Realization.lcCompactSpace (X × Y) ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι :=
  (TensorCommutant.Realization.testPullback e).trans (finiteTestSpaceEquiv ι)

variable (q : ℕ) [Fact q.Prime]
variable {ι X : Type*} [Fintype ι] [TopologicalSpace X] [T2Space X]

/-- The full local test-space automorphism acts section by section in the
split finite-adelic chart. This defines an actual operator on every test function. -/
def finiteLocalOperatorHom (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × X) :
    (Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3 ≃ₗ[ℂ]
      Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3) →*
        (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :=
  (TensorCommutant.Realization.conjugateLinearAut (finiteProductTestEquiv e)).comp
    (TensorCommutant.Realization.extendTestHom.comp (TensorCommutant.Realization.conjugateLinearAut (nonarchTestSpaceEquiv ℚ_[q] 3).symm))

theorem finiteLocalOperatorHom_tensor (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × X)
    (U : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3 ≃ₗ[ℂ]
      Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3)
    (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q)) (g : TestSections.Realization.lcCompactSpace X) :
    finiteLocalOperatorHom q e U (finiteProductTestEquiv e (TensorCommutant.Realization.tensorTest f g)) =
      finiteProductTestEquiv e (TensorCommutant.Realization.tensorTest
        ((nonarchTestSpaceEquiv ℚ_[q] 3).symm (U (nonarchTestSpaceEquiv ℚ_[q] 3 f))) g) := by
  let E := finiteProductTestEquiv e
  let L := nonarchTestSpaceEquiv ℚ_[q] 3
  change E (TensorCommutant.Realization.extendTestHom (TensorCommutant.Realization.conjugateLinearAut L.symm U)
    (E.symm (E (TensorCommutant.Realization.tensorTest f g)))) = E (TensorCommutant.Realization.tensorTest (L.symm (U (L f))) g)
  rw [E.symm_apply_apply, TensorCommutant.Realization.extendTestHom_tensor]
  rfl

theorem finiteLocalOperatorHom_neg (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × X) :
    finiteLocalOperatorHom q e (LinearEquiv.neg ℂ) = LinearEquiv.neg ℂ := by
  unfold finiteLocalOperatorHom
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, TensorCommutant.Realization.conjugateLinearAut_neg, TensorCommutant.Realization.extendTestHom_neg, TensorCommutant.Realization.conjugateLinearAut_neg]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization

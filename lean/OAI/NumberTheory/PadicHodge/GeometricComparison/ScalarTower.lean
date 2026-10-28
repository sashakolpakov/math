import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarTowerSubspace
import OAI.NumberTheory.PadicHodge.GeometricComparison.EquivOperatorTransport

/-! # Scalar Tower -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarTower.ScalarComparisonTower

noncomputable section

/-! Extending a genuine scalar comparison again preserves its operators and actual filtration subspaces. -/

open scoped TensorProduct

variable (K Q L : Type*) [Field K] [Field Q] [Field L]
  [Algebra K Q] [Algebra K L] [Algebra Q L] [IsScalarTower K Q L]
  {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module Q W]

def equiv (e : Q ⊗[K] V ≃ₗ[Q] W) : L ⊗[K] V ≃ₗ[L] L ⊗[Q] W :=
  (ScalarTowerSubspace.ScalarTowerComparison.equiv K Q L V).symm.trans (e.baseChange Q L _ _)

omit [Algebra K L] [IsScalarTower K Q L] in
theorem baseChange_intertwines (e : Q ⊗[K] V ≃ₗ[Q] W)
    (T : Module.End Q (Q ⊗[K] V)) (U : Module.End Q W)
    (h : ∀ x, e (T x) = U (e x)) (x : L ⊗[Q] (Q ⊗[K] V)) :
    (e.baseChange Q L _ _) (T.baseChange L x) = U.baseChange L ((e.baseChange Q L _ _) x) := by
  have he : e.toLinearMap.comp T = U.comp e.toLinearMap := LinearMap.ext h
  have hb := congrArg (fun f : (Q ⊗[K] V) →ₗ[Q] W => f.baseChange L) he
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hb
  exact LinearMap.congr_fun hb x

theorem naturality (e : Q ⊗[K] V ≃ₗ[Q] W) (T : Module.End K V) (U : Module.End Q W)
    (h : ∀ x, e (T.baseChange Q x) = U (e x)) (x : L ⊗[K] V) :
    equiv K Q L e (T.baseChange L x) = U.baseChange L (equiv K Q L e x) := by
  let a := ScalarTowerSubspace.ScalarTowerComparison.equiv K Q L V
  let b := e.baseChange Q L (Q ⊗[K] V) W
  have ha := EquivOperatorTransport.inverse_intertwines a.toEquiv ((T.baseChange Q).baseChange L) (T.baseChange L)
    (fun y => LinearMap.congr_fun (ScalarTowerSubspace.ScalarTowerComparison.naturality K Q L T) y) x
  exact (congrArg b ha).trans (baseChange_intertwines K Q L e (T.baseChange Q) U h (a.symm x))

theorem subspace (e : Q ⊗[K] V ≃ₗ[Q] W) (P : Submodule K V) (F : Submodule Q W)
    (h : (P.baseChange Q).map e.toLinearMap = F) :
    (P.baseChange L).map (equiv K Q L e).toLinearMap = F.baseChange L := by
  let a := ScalarTowerSubspace.ScalarTowerComparison.equiv K Q L V
  have ha : (P.baseChange L).map a.symm.toLinearMap = (P.baseChange Q).baseChange L :=
    (Submodule.map_symm_eq_iff a).mpr (ScalarTowerSubspace.ScalarTowerComparison.subspace K Q L P)
  have hb : ((P.baseChange Q).baseChange L).map (e.toLinearMap.baseChange L) = F.baseChange L :=
    (ScalarExtension.ScalarExtensionRanges.map L (P.baseChange Q) e.toLinearMap).symm.trans
      (congrArg (Submodule.baseChange L) h)
  change (P.baseChange L).map ((e.toLinearMap.baseChange L).comp a.symm.toLinearMap) = _
  rw [Submodule.map_comp, ha]
  exact hb

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarTower.ScalarComparisonTower

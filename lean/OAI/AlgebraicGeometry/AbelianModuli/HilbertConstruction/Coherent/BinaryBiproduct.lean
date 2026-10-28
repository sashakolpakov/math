import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BinaryBiproductCoproduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType

/-! # Binary Biproduct -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.BinaryBiproduct

noncomputable section

/-! Binary biproducts preserve quasicoherence and finite type, using universe-correct finite coproducts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def liftedTwoCoproductIsoBiprod {X : Scheme.{u}} (M N : X.Modules) :
    (∐ fun i : ULift.{u} (Fin 2) ↦ ![M, N] i.down) ≅ M ⊞ N :=
  Sigma.reindex Equiv.ulift ![M, N] ≪≫ BinaryBiproductCoproduct.finTwoCoproductIsoBiprod M N

theorem module_biprod_quasicoherent {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent := by
  have hq : (∐ fun i : ULift.{u} (Fin 2) ↦ ![M, N] i.down).IsQuasicoherent :=
    Quasicoherent.Coproducts.module_quasicoherent_coproduct _ (fun ⟨i⟩ ↦ by fin_cases i <;> dsimp <;> infer_instance)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (liftedTwoCoproductIsoBiprod M N) hq

theorem module_biprod_finiteType {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType] : (M ⊞ N).IsFiniteType := by
  have : (∐ fun i : ULift.{u} (Fin 2) ↦ ![M, N] i.down).IsQuasicoherent :=
    Quasicoherent.Coproducts.module_quasicoherent_coproduct _ (fun ⟨i⟩ ↦ by fin_cases i <;> dsimp <;> infer_instance)
  have : (∐ fun i : ULift.{u} (Fin 2) ↦ ![M, N] i.down).IsFiniteType :=
    Quasicoherent.FiniteCoproducts.module_finiteType_finite_coproduct _
      (fun ⟨i⟩ ↦ by fin_cases i <;> dsimp <;> infer_instance)
      (fun ⟨i⟩ ↦ by fin_cases i <;> dsimp <;> infer_instance)
  have : (M ⊞ N).IsQuasicoherent := module_biprod_quasicoherent M N
  exact Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso (liftedTwoCoproductIsoBiprod M N)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.BinaryBiproduct

import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.HorizontalHomotopyEdge
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total

/-! # Local Cech Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechTotal.SemilatticeLocalCechTotal

noncomputable section

/-! The canonical local Čech total augmentation is a quasi-isomorphism
when the original chart augmentation is and intersections preserve coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z
variable (R : Type u) [CommRing R] (C : Type v) [SemilatticeInf C]
  {D : Type w} [Category.{z} D] {ι : Type} (U : ι → C) (i : ι)
  (P : Cᵒᵖ ⥤ CochainComplex (D ⥤ ModuleCat.{u} R) ℕ)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op))

def chartEdge : P.obj (op (U i)) ⟶ CechCone.Total.CechConeTotal.total U P :=
  HorizontalHomotopyEdge.HorizontalHomotopyTotalEdge.edge R (P.obj (op (U i))) (CechCone.Total.CechConeTotal.horizontal U P)
    (LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv C U i P h)

theorem chartEdge_quasiIso : QuasiIso (chartEdge R C U i P h) :=
  HorizontalHomotopyEdge.HorizontalHomotopyTotalEdge.quasiIso R (P.obj (op (U i))) (CechCone.Total.CechConeTotal.horizontal U P)
    (LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv C U i P h)

variable (M : CochainComplex (D ⥤ ModuleCat.{u} R) ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

theorem zeroMap_factorization : CechCone.Total.CechConeTotal.zeroMap U P M η =
    η.app (op (U i)) ≫ (LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv C U i P h).hom.f 0 := by
  have hh := congrArg (fun α => α.f 0)
    (LocalCechAugmentation.SemilatticeLocalCechAugmentation.homotopy_factorization C U i P M η h)
  rw [NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero, HomologicalComplex.comp_f,
    CochainComplex.single₀_map_f_zero] at hh
  exact hh

theorem augmentation_factorization : CechCone.Total.CechConeTotal.augmentation U P M η =
    η.app (op (U i)) ≫ chartEdge R C U i P h := by
  ext q : 1
  have hq := congrArg (fun α => α.f q) (zeroMap_factorization R C U i P h M η)
  change CechCone.Total.CechConeTotal.component U P M η q = (η.app (op (U i))).f q ≫
    ((LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv C U i P h).hom.f 0).f q at hq
  change CechCone.Total.CechConeTotal.component U P M η q ≫ (CechCone.Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl =
    (η.app (op (U i))).f q ≫
      ((LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv C U i P h).hom.f 0).f q ≫
        (CechCone.Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl
  exact (congrArg (fun α => α ≫ (CechCone.Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl) hq).trans
    (Category.assoc _ _ _)

include h in
theorem quasiIso [QuasiIso (η.app (op (U i)))] : QuasiIso (CechCone.Total.CechConeTotal.augmentation U P M η) := by
  let := chartEdge_quasiIso R C U i P h
  rw [augmentation_factorization R C U i P h M η]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechTotal.SemilatticeLocalCechTotal

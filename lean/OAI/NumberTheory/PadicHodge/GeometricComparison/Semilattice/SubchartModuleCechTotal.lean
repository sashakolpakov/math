import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartCechAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.HomotopyTotalEdge
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total

/-! # Subchart Module Cech Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartModuleCechTotal.SemilatticeSubchartModuleCechTotal

noncomputable section

/-! The canonical local Čech total augmentation is a quasi-isomorphism
when the original chart augmentation is and intersections preserve coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable (R : Type u) [CommRing R] (C : Type v) [SemilatticeInf C]
  {ι : Type} (U : ι → C) (I : C) (i : ι) (hi : I ≤ U i)
  (P : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max u w} R) ℕ)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

def chartEdge : P.obj (op I) ⟶ CechCone.Total.CechConeTotal.total U P :=
  Module.HomotopyTotalEdge.ModuleHomotopyTotalEdge.edge R (P.obj (op I)) (CechCone.Total.CechConeTotal.horizontal U P)
    (SubchartCechContraction.SemilatticeSubchartCechContraction.homotopyEquiv C U I P h i hi)

theorem chartEdge_quasiIso : QuasiIso (chartEdge R C U I i hi P h) :=
  Module.HomotopyTotalEdge.ModuleHomotopyTotalEdge.quasiIso R (P.obj (op I)) (CechCone.Total.CechConeTotal.horizontal U P)
    (SubchartCechContraction.SemilatticeSubchartCechContraction.homotopyEquiv C U I P h i hi)

variable (M : CochainComplex (ModuleCat.{max u w} R) ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

theorem zeroMap_factorization : CechCone.Total.CechConeTotal.zeroMap U P M η =
    η.app (op I) ≫ (SubchartCechContraction.SemilatticeSubchartCechContraction.homotopyEquiv C U I P h i hi).hom.f 0 := by
  have hh := congrArg (fun α => α.f 0)
    (SubchartCechAugmentation.SemilatticeSubchartCechAugmentation.homotopy_factorization C U I P M η h i hi)
  rw [NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero, HomologicalComplex.comp_f,
    CochainComplex.single₀_map_f_zero] at hh
  exact hh

theorem augmentation_factorization : CechCone.Total.CechConeTotal.augmentation U P M η =
    η.app (op I) ≫ chartEdge R C U I i hi P h := by
  ext q : 1
  have hq := congrArg (fun α => α.f q) (zeroMap_factorization R C U I i hi P h M η)
  change CechCone.Total.CechConeTotal.component U P M η q = (η.app (op I)).f q ≫
    ((SubchartCechContraction.SemilatticeSubchartCechContraction.homotopyEquiv C U I P h i hi).hom.f 0).f q at hq
  change CechCone.Total.CechConeTotal.component U P M η q ≫ (CechCone.Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl =
    (η.app (op I)).f q ≫
      ((SubchartCechContraction.SemilatticeSubchartCechContraction.homotopyEquiv C U I P h i hi).hom.f 0).f q ≫
        (CechCone.Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl
  exact (congrArg (fun α => α ≫ (CechCone.Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q 0 q rfl) hq).trans
    (Category.assoc _ _ _)

include h hi in
theorem quasiIso [QuasiIso (η.app (op I))] : QuasiIso (CechCone.Total.CechConeTotal.augmentation U P M η) := by
  let := chartEdge_quasiIso R C U I i hi P h
  rw [augmentation_factorization R C U I i hi P h M η]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartModuleCechTotal.SemilatticeSubchartModuleCechTotal

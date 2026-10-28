/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafTerms.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafTerms

/-! # Sheaf Forget Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafForgetProjection

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u v w
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X) {ι : Type u}
variable (U : ι → Opens X) (n : ℕ)

theorem cechTermForgetIso_hom_π (i : Fin (n + 1) → ι) :
    (SheafTerms.cechTermForgetIso F U n).hom ≫
        Pi.π (fun i : Fin (n + 1) → ι => (SheafTerms.cechTermFactor F U n i).obj) i =
      (Pi.π (SheafTerms.cechTermFactor F U n) i).hom := by
  change (SheafTerms.cechTermForgetIso F U n).hom ≫
      limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
        (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩ =
      (TopCat.Sheaf.forget AddCommGrpCat X).map
        (limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n)) ⟨i⟩)
  let : HasLimit (Discrete.functor (SheafTerms.cechTermFactor F U n) ⋙
      TopCat.Sheaf.forget AddCommGrpCat X) := hasLimit_of_iso
    (SheafTerms.cechTermForgetDiagramIso F U n).symm
  have hnat :
      (HasLimit.isoOfNatIso (SheafTerms.cechTermForgetDiagramIso F U n)).hom ≫
          limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩ =
        limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n) ⋙
          TopCat.Sheaf.forget AddCommGrpCat X) ⟨i⟩ := by
    have happ : (SheafTerms.cechTermForgetDiagramIso F U n).hom.app ⟨i⟩ =
        𝟙 ((SheafTerms.cechTermFactor F U n i).obj) := rfl
    have hbase :
        (HasLimit.isoOfNatIso (SheafTerms.cechTermForgetDiagramIso F U n)).hom ≫
            limit.π (Discrete.functor fun i : Fin (n + 1) → ι ↦
              (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩ =
          limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n) ⋙
              TopCat.Sheaf.forget AddCommGrpCat X) ⟨i⟩ ≫
            (SheafTerms.cechTermForgetDiagramIso F U n).hom.app ⟨i⟩ :=
      HasLimit.isoOfNatIso_hom_π (SheafTerms.cechTermForgetDiagramIso F U n) ⟨i⟩
    have hcomp : limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n) ⋙
          TopCat.Sheaf.forget AddCommGrpCat X) ⟨i⟩ ≫
          (SheafTerms.cechTermForgetDiagramIso F U n).hom.app ⟨i⟩ =
        limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n) ⋙
          TopCat.Sheaf.forget AddCommGrpCat X) ⟨i⟩ := by
      rw [happ]
      exact Category.comp_id _
    exact hbase.trans hcomp
  have hpreserves :
      (preservesLimitIso (TopCat.Sheaf.forget AddCommGrpCat X)
          (Discrete.functor (SheafTerms.cechTermFactor F U n))).hom ≫
          limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n) ⋙
            TopCat.Sheaf.forget AddCommGrpCat X) ⟨i⟩ =
        (TopCat.Sheaf.forget AddCommGrpCat X).map
          (limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n)) ⟨i⟩) :=
    preservesLimitIso_hom_π (TopCat.Sheaf.forget AddCommGrpCat X)
      (Discrete.functor (SheafTerms.cechTermFactor F U n)) ⟨i⟩
  have hcombined :
      (preservesLimitIso (TopCat.Sheaf.forget AddCommGrpCat X)
          (Discrete.functor (SheafTerms.cechTermFactor F U n))).hom ≫
          ((HasLimit.isoOfNatIso (SheafTerms.cechTermForgetDiagramIso F U n)).hom ≫
            limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
              (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩) =
        (TopCat.Sheaf.forget AddCommGrpCat X).map
          (limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n)) ⟨i⟩) := by
    rw [hnat]
    exact hpreserves
  change
    (preservesLimitIso (TopCat.Sheaf.forget AddCommGrpCat X)
        (Discrete.functor (SheafTerms.cechTermFactor F U n))).hom ≫
        ((HasLimit.isoOfNatIso (SheafTerms.cechTermForgetDiagramIso F U n)).hom ≫
          limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩) =
      (TopCat.Sheaf.forget AddCommGrpCat X).map
        (limit.π (Discrete.functor (SheafTerms.cechTermFactor F U n)) ⟨i⟩)
  exact hcombined

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafForgetProjection

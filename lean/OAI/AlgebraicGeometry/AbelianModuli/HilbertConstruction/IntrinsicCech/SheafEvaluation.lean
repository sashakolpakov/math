/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafTerms.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafForgetProjection

/-! # Sheaf Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafEvaluation

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u v w
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X) {ι : Type u}
variable (U : ι → Opens X) (n : ℕ)

noncomputable def cechTermForgetSectionsIso (V : Opens X) :
    (SheafTerms.cechTerm F U n).obj.obj (op V) ≅
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).obj
        (∏ᶜ fun i : Fin (n + 1) → ι => (SheafTerms.cechTermFactor F U n i).obj) :=
  ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).mapIso
    (SheafTerms.cechTermForgetIso F U n)

noncomputable def cechTermEvaluationDiagramIso (V : Opens X) :
    (Discrete.functor fun i : Fin (n + 1) → ι =>
        (SheafTerms.cechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V) ≅
      Discrete.functor fun i : Fin (n + 1) → ι =>
        (SheafTerms.cechTermFactor F U n i).obj.obj (op V) :=
  Discrete.natIso (fun _ => Iso.refl _)

noncomputable def cechTermEvaluationIso (V : Opens X) :
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).obj
        (∏ᶜ fun i : Fin (n + 1) → ι => (SheafTerms.cechTermFactor F U n i).obj) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (SheafTerms.cechTermFactor F U n i).obj.obj (op V) := by
  letI : HasLimit (Discrete.functor
      (fun i : Fin (n + 1) → ι => (SheafTerms.cechTermFactor F U n i).obj) ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) :=
    hasLimit_of_iso (cechTermEvaluationDiagramIso F U n V).symm
  exact preservesLimitIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
      (Discrete.functor fun i : Fin (n + 1) → ι => (SheafTerms.cechTermFactor F U n i).obj) ≪≫
    HasLimit.isoOfNatIso (cechTermEvaluationDiagramIso F U n V)

theorem cechTermEvaluationIso_hom_π (V : Opens X)
    (i : Fin (n + 1) → ι) :
    (cechTermEvaluationIso F U n V).hom ≫
        Pi.π (fun i : Fin (n + 1) → ι =>
          (SheafTerms.cechTermFactor F U n i).obj.obj (op V)) i =
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
        (Pi.π (fun i : Fin (n + 1) → ι =>
          (SheafTerms.cechTermFactor F U n i).obj) i) := by
  change (cechTermEvaluationIso F U n V).hom ≫
      limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
        (SheafTerms.cechTermFactor F U n i).obj.obj (op V)) ⟨i⟩ =
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
        (limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
          (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩)
  let : HasLimit ((Discrete.functor fun i : Fin (n + 1) → ι =>
      (SheafTerms.cechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) := hasLimit_of_iso
    (cechTermEvaluationDiagramIso F U n V).symm
  have hnat :
      (HasLimit.isoOfNatIso (cechTermEvaluationDiagramIso F U n V)).hom ≫
          limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj.obj (op V)) ⟨i⟩ =
        limit.π ((Discrete.functor fun i : Fin (n + 1) → ι =>
          (SheafTerms.cechTermFactor F U n i).obj) ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) ⟨i⟩ := by
    calc
      _ = limit.π ((Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj) ⋙
              (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) ⟨i⟩ ≫
          (cechTermEvaluationDiagramIso F U n V).hom.app ⟨i⟩ :=
        HasLimit.isoOfNatIso_hom_π (cechTermEvaluationDiagramIso F U n V) ⟨i⟩
      _ = _ := Category.comp_id _
  have hpreserves :
      (preservesLimitIso
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
          (Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj)).hom ≫
          limit.π ((Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj) ⋙
              (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) ⟨i⟩ =
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
          (limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩) :=
    preservesLimitIso_hom_π
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
      (Discrete.functor fun i : Fin (n + 1) → ι =>
        (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩
  have hcombined :
      (preservesLimitIso
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
          (Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj)).hom ≫
          ((HasLimit.isoOfNatIso (cechTermEvaluationDiagramIso F U n V)).hom ≫
            limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
              (SheafTerms.cechTermFactor F U n i).obj.obj (op V)) ⟨i⟩) =
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
          (limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (SheafTerms.cechTermFactor F U n i).obj) ⟨i⟩) := by
    rw [hnat]
    exact hpreserves
  simpa only [cechTermEvaluationIso, Iso.trans_hom, Category.assoc] using hcombined

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafEvaluation

import OAI.AlgebraicGeometry.Picard.PoincareBundle.TranslationDefectChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit

/-! # Translation Symmetry Independence -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TranslationSymmetryIndependence

noncomputable section

/-! Symmetry of the regular defect is independent of the chosen subgroup translation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t s : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

theorem symmetry_of_symmetry {T : Over (Spec (.of k))} (a b : T ⟶ H)
    (ht : Subgroup.DefectParameters.value i L t a b = Subgroup.DefectParameters.value i L t b a) : Subgroup.DefectParameters.value i L s a b = Subgroup.DefectParameters.value i L s b a := by
  let r := fun c : T ⟶ H => Subgroup.TranslationRatio.value i L t s c
  have hab := TranslationDefectChange.coboundary i L t s a b
  have hba := TranslationDefectChange.coboundary i L t s b a
  have h : (r a * r b) * Subgroup.DefectParameters.value i L s a b = (r a * r b) * Subgroup.DefectParameters.value i L s b a := by
    calc
      (r a * r b) * Subgroup.DefectParameters.value i L s a b = Subgroup.DefectParameters.value i L t a b * r (a * b) := hab.symm
      _ = Subgroup.DefectParameters.value i L t b a * r (b * a) := congrArg₂ (· * ·) ht (congrArg r (mul_comm a b))
      _ = (r b * r a) * Subgroup.DefectParameters.value i L s b a := hba
      _ = (r a * r b) * Subgroup.DefectParameters.value i L s b a := congrArg (fun d => d * Subgroup.DefectParameters.value i L s b a) (mul_comm (r b) (r a))
  exact mul_left_cancel h

/-- Neither a subgroup frame choice nor a regular scalar correction changes defect symmetry. -/
theorem symmetry_iff {T : Over (Spec (.of k))} (a b : T ⟶ H) :
    Subgroup.DefectParameters.value i L t a b = Subgroup.DefectParameters.value i L t b a ↔ Subgroup.DefectParameters.value i L s a b = Subgroup.DefectParameters.value i L s b a :=
  ⟨symmetry_of_symmetry i L t s a b, symmetry_of_symmetry i L s t a b⟩

/-- The identity normalization used for effective descent preserves and reflects symmetry. -/
theorem normalized_symmetry_iff {T : Over (Spec (.of k))} (a b : T ⟶ H) :
    Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t) a b =
        Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t) b a ↔
      Subgroup.DefectParameters.value i L t a b = Subgroup.DefectParameters.value i L t b a :=
  symmetry_iff i L (NormalizedTranslationUnit.translation i L t) t a b

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TranslationSymmetryIndependence

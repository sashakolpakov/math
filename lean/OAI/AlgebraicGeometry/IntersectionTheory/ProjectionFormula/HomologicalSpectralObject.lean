import Mathlib.CategoryTheory.Triangulated.SpectralObject
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.SpectralObject.Basic

/-! # Homological Spectral Object -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologicalSpectralObject

noncomputable section

/-! Applying a homological functor to the distinguished triangles of a
spectral object constructs an abelian spectral object with the actual
connecting maps and long exact sequences. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated

variable {C A ι : Type*} [Category* C] [Category* A] [Category* ι]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Abelian A]
  (X : Triangulated.SpectralObject C ι) (F : C ⥤ A)
  [F.IsHomological] [F.ShiftSequence ℤ]

def spectralObject : Abelian.SpectralObject A ι where
  H n := X.ω₁ ⋙ F.shift n
  δ' n₀ n₁ h :=
    { app D := F.homologySequenceδ (X.ω₂.obj D) n₀ n₁ h
      naturality _ _ φ :=
        F.homologySequenceδ_naturality (X.ω₂.map φ) n₀ n₁ h }
  exact₁' n₀ n₁ h D :=
    (F.homologySequence_exact₁ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows
  exact₂' n D :=
    (F.homologySequence_exact₂ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n).exact_toComposableArrows
  exact₃' n₀ n₁ h D :=
    (F.homologySequence_exact₃ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologicalSpectralObject

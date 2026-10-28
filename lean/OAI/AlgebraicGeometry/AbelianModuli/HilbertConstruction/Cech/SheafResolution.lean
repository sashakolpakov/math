/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafResolution.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PositiveCycleStalks

/-! # Sheaf Resolution -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafResolution.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

theorem cechAugmentation_app_injective (hU : ⨆ i, U i = ⊤) (V : Opens X) :
    Function.Injective ((SheafAugmentation.IntrinsicCech.cechAugmentation F U).hom.app (op V)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply TopCat.Presheaf.IsSheaf.section_ext F.2
  intro x hxV
  have hxCover : x ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  obtain ⟨i₀, hxi₀⟩ := Opens.mem_iSup.mp hxCover
  let i : Fin 1 → ι := fun _ => i₀
  let W : Opens X := V ⊓ (∏ᶜ fun k : Fin 1 => U (i k))
  have hWV : W ≤ V := inf_le_left
  refine ⟨W, hWV, ?_, ?_⟩
  · exact ⟨hxV, by simpa [i, ZeroCycleIndices.IntrinsicCech.cechSingletonIntersection_eq U i] using hxi₀⟩
  · have hi := congrArg (fun y => IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V y i) hs
    rw [SheafAugmentation.IntrinsicCech.cechAugmentation_apply, map_zero, Pi.zero_apply] at hi
    simpa [W] using hi

/-- If the opens `U i` cover the whole space, the Cech augmentation is a monomorphism. -/
theorem cechAugmentation_mono (hU : ⨆ i, U i = ⊤) : Mono (SheafAugmentation.IntrinsicCech.cechAugmentation F U) := by
  refine CategoryTheory.Sheaf.mono_of_injective _ ?_
  intro V
  exact cechAugmentation_app_injective F U hU V.unop

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafResolution.IntrinsicCech

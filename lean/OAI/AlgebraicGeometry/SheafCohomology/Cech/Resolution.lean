/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafResolution.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveExact

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.Resolution.TopCat.Sheaf

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Monicity of the sheaf-level Cech augmentation

This file proves that the augmentation into the sheaf-level Cech complex is monic for an
open cover.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private theorem cechSingletonIntersection_eq (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 1 => U (i k)) = U (i 0) := by
  apply le_antisymm
  · exact leOfHom (Pi.π (fun k : Fin 1 => U (i k)) 0)
  · exact leOfHom (Pi.lift fun k : Fin 1 => homOfLE (by
      rw [Subsingleton.elim k 0]))

private theorem cechAugmentation_app_injective (hU : ⨆ i, U i = ⊤) (V : Opens X) :
    Function.Injective ((Augmentation.TopCat.Sheaf.cechAugmentation F U).hom.app (op V)) := by
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
  · exact ⟨hxV, by simpa [i, cechSingletonIntersection_eq U i] using hxi₀⟩
  · have hi := congrArg (fun y => Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U 0 V y i) hs
    rw [Augmentation.TopCat.Sheaf.cechAugmentation_apply, map_zero, Pi.zero_apply] at hi
    simpa [W] using hi

/-- If the opens `U i` cover the whole space, the Cech augmentation is a monomorphism. -/
theorem cechAugmentation_mono (hU : ⨆ i, U i = ⊤) : Mono (Augmentation.TopCat.Sheaf.cechAugmentation F U) := by
  refine CategoryTheory.Sheaf.mono_of_injective _ ?_
  intro V
  exact cechAugmentation_app_injective F U hU V.unop

end OAI.AlgebraicGeometry.SheafCohomology.Cech.Resolution.TopCat.Sheaf

import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Normalized Translation Unit -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit

noncomputable section

/-! The normalized subgroup translation satisfies the native descent unit diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open Pseudofunctor.LocallyDiscreteOpToCat

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [GrpObj A]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

/-- Identity-normalized actual subgroup translation, expressed in the PoincareBundle fiber API. -/
def translation : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i) := NormalizedKernelTranslation.normalized i (Line.Comparison.Bundle.toShared L) t

theorem unit_diagram :
    pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
      (f₁ := snd H A) (f₂ := NormalizedKernelTranslation.action i) (translation i L t).hom
      (NormalizedKernelTranslation.sectionMap (H := H) (A := A)) (𝟙 A) (𝟙 A)
      (NormalizedKernelTranslation.section_source (H := H) (A := A)) (NormalizedKernelTranslation.section_action i) = 𝟙 (Line.Fibers.fiber L (𝟙 A)) := by
  let s := NormalizedKernelTranslation.sectionMap (H := H) (A := A)
  let ex := Line.Fibers.fiberPullbackIso L s (snd H A) (𝟙 A) (NormalizedKernelTranslation.section_source (H := H) (A := A))
  let ey := Line.Fibers.fiberPullbackIso L s (NormalizedKernelTranslation.action i) (𝟙 A) (NormalizedKernelTranslation.section_action i)
  let e := (Scheme.Modules.pullbackId A.left).app L.sheaf
  have hn : (Scheme.Modules.pullback s.left).map (translation i L t).hom ≫ (ey.hom ≫ e.hom) =
      ex.hom ≫ e.hom := NormalizedKernelTranslation.normalized_unit i (Line.Comparison.Bundle.toShared L) t
  have hc : (Scheme.Modules.pullback s.left).map (translation i L t).hom ≫ ey.hom = ex.hom := by
    apply (cancel_mono e.hom).mp
    exact (Category.assoc _ _ _).trans hn
  have hp := Line.Fibers.pullHom_eq L (x := snd H A) (y := NormalizedKernelTranslation.action i)
    (translation i L t).hom s (𝟙 A) (𝟙 A)
    (NormalizedKernelTranslation.section_source (H := H) (A := A)) (NormalizedKernelTranslation.section_action i)
  exact hp.trans ((congrArg (fun m => ex.inv ≫ m) hc).trans ex.inv_hom_id)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit

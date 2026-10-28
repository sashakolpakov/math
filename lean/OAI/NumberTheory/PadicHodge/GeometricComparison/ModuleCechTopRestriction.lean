import OAI.NumberTheory.PadicHodge.GeometricComparison.LargeCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionCoefficients
import OAI.NumberTheory.PadicHodge.GeometricComparison.LargeModuleAt

/-! # Module Cech Top Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ModuleCechTopRestriction.LargeModuleCechTopRestriction

noncomputable section

/-! The canonical top-section augmentation is exact and injective for module sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v w
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R))
  {ι : Type} (U : ι → Opens X)

theorem exact_and_mono (hU : iSup U = ⊤) :
    (Cech.TopRestriction.CechTopRestriction.initial (Opens X) U F.obj).Exact ∧
      Mono (Cech.TopRestriction.CechTopRestriction.map (Opens X) U F.obj) := by
  let G := forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}
  have h := LargeCech.LargeCechTopRestriction.small.{v, max u w} X
    (LargeModuleAt.LargeModuleFlasqueCech.underlyingSheaf R X F) U hU
  have hm := (ShortComplex.exact_and_mono_f_iff_of_iso
    (Cech.TopRestrictionCoefficients.CechTopRestrictionCoefficients.initialIso (Opens X) G U F.obj)).mpr h
  refine ⟨(ShortComplex.moduleCat_exact_iff _).mpr ((ShortComplex.ab_exact_iff _).mp hm.1), ?_⟩
  exact (ModuleCat.mono_iff_injective _).mpr ((AddCommGrpCat.mono_iff_injective _).mp hm.2)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ModuleCechTopRestriction.LargeModuleCechTopRestriction

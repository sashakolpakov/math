import OAI.NumberTheory.PadicHodge.GeometricComparison.HomeomorphSheaf
import OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueExact
import Mathlib.Topology.Category.TopCat.ULift

/-! # Large Flasque -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LargeFlasque.LargeFlasqueCech

noncomputable section

/-! Flasque Cech exactness for large coefficient groups on a smaller space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v
variable (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{max u v} X)
  {ι : Type (max u v)} (U : ι → Opens X)

def homeomorphism : X ≃ₜ ULift.{v} X := Homeomorph.ulift.symm

def liftedSheaf : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of (ULift.{v} X)) :=
  (HomeomorphSheaf.HomeomorphSheafTransport.transport (homeomorphism.{u, v} X) AddCommGrpCat.{max u v}).obj F

instance lifted_flasque [TopCat.Sheaf.IsFlasque F] : TopCat.Sheaf.IsFlasque (liftedSheaf X F) := by
  let : TopCat.Presheaf.IsFlasque (X := TopCat.of X) F.obj := ‹TopCat.Sheaf.IsFlasque F›
  exact HomeomorphSheaf.HomeomorphSheafTransport.transport_flasque (homeomorphism.{u, v} X) AddCommGrpCat.{max u v} F

theorem exactAt_succ [TopCat.Sheaf.IsFlasque F] (hU : iSup U = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) := by
  let e := homeomorphism.{u, v} X
  let V : ι → Opens (ULift.{v} X) := (HomeomorphSheaf.HomeomorphSheafTransport.opens e).obj ∘ U
  have hV : iSup V = ⊤ := HomeomorphSheaf.HomeomorphSheafTransport.cover e.symm U hU
  have h := AlgebraicGeometry.SheafCohomology.Cech.FlasqueExact.TopCat.Sheaf.cechComplex_exactAt_succ_of_isFlasque (liftedSheaf X F) V hV n
  have he : (HomeomorphSheaf.HomeomorphSheafTransport.opens e.symm).obj ∘ V = U := by
    funext i
    exact e.opensCongr.symm_apply_apply (U i)
  have hex := h.of_iso (HomeomorphSheaf.HomeomorphSheafTransport.cechIso e AddCommGrpCat.{max u v} V F)
  simpa only [he] using hex

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LargeFlasque.LargeFlasqueCech

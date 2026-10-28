import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.LargeFlasque

/-! # Large Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LargeCech.LargeCechTopRestriction

noncomputable section

/-! Degree-zero sheaf descent for large coefficient groups and arbitrary small covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u v
variable (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{max u v} X)

theorem large {ι : Type (max u v)} (U : ι → Opens X) (hU : iSup U = ⊤) :
    (Cech.TopRestriction.CechTopRestriction.initial (Opens X) U F.obj).Exact ∧
      Mono (Cech.TopRestriction.CechTopRestriction.map (Opens X) U F.obj) := by
  let e := LargeFlasque.LargeFlasqueCech.homeomorphism.{u, v} X
  let V : ι → Opens (ULift.{v} X) := (HomeomorphSheaf.HomeomorphSheafTransport.opens e).obj ∘ U
  let G := LargeFlasque.LargeFlasqueCech.liftedSheaf X F
  have hV : iSup V = ⊤ := HomeomorphSheaf.HomeomorphSheafTransport.cover e.symm U hU
  have he : (HomeomorphSheaf.HomeomorphSheafTransport.opens e.symm).obj ∘ V = U := by
    funext i
    exact e.opensCongr.symm_apply_apply (U i)
  let et : (HomeomorphSheaf.HomeomorphSheafTransport.opens e.symm).obj ⊤ ≅ ⊤ :=
    eqToIso e.symm.opensCongr.map_top
  have h : (Cech.TopRestriction.CechTopRestriction.initial (Opens (ULift.{v} X)) V G.obj).Exact ∧
      Mono (Cech.TopRestriction.CechTopRestriction.map (Opens (ULift.{v} X)) V G.obj) :=
    ⟨Cech.TopRestriction.CechTopRestriction.exact _ G V hV, Cech.TopRestriction.CechTopRestriction.mono _ G V hV⟩
  have hh := (ShortComplex.exact_and_mono_f_iff_of_iso
    (Cech.TopRestrictionBaseChange.CechTopRestrictionBaseChange.initialIso (HomeomorphSheaf.HomeomorphSheafTransport.opens e.symm) et V F.obj)).mp h
  change (Cech.TopRestriction.CechTopRestriction.initial (Opens X)
      ((HomeomorphSheaf.HomeomorphSheafTransport.opens e.symm).obj ∘ V) F.obj).Exact ∧
    Mono (Cech.TopRestriction.CechTopRestriction.map (Opens X)
      ((HomeomorphSheaf.HomeomorphSheafTransport.opens e.symm).obj ∘ V) F.obj) at hh
  exact (congrArg (fun W => (Cech.TopRestriction.CechTopRestriction.initial (Opens X) W F.obj).Exact ∧
    Mono (Cech.TopRestriction.CechTopRestriction.map (Opens X) W F.obj)) he).mp hh

theorem small {ι : Type} (U : ι → Opens X) (hU : iSup U = ⊤) :
    (Cech.TopRestriction.CechTopRestriction.initial (Opens X) U F.obj).Exact ∧
      Mono (Cech.TopRestriction.CechTopRestriction.map (Opens X) U F.obj) := by
  let e : ULift.{max u v} ι ≃ ι := Equiv.ulift
  have hV : iSup (U ∘ e) = ⊤ := e.iSup_comp.trans hU
  exact (ShortComplex.exact_and_mono_f_iff_of_iso
    (Cech.TopRestrictionReindex.CechTopRestrictionReindex.initialIso (Opens X) e U F.obj)).mp (large X F (U ∘ e) hV)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LargeCech.LargeCechTopRestriction

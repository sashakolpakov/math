import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CoverRefinementQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechCoverRefinement

/-! # Cech Open Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechOpenCoverRefinement.Base

noncomputable section

/-! The same-open refinement theorem for the original base-linear
module Čech complex, with its literal coefficient structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open Scheme.Modules OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechCoverRefinement

universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι κ : Type u} (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (M : X.Modules) [M.IsQuasicoherent] (O : X.Opens)

theorem quasiIso (hU : iSup U = O) (hV : iSup V = O)
    (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i)) :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M)) := by
  let G : ModuleCat.{u} Γ(S, ⊤) ⥤ AddCommGrpCat.{u} := forget₂ _ _
  have hq : QuasiIso (Cech.CoverRefinement.map U V r M.presheaf) :=
    Open.CoverRefinementQuasiIso.Cech.quasiIso U V r M O hU hV haU haV
  rw [_root_.quasiIso_iff]
  intro n
  let : IsIso (HomologicalComplex.homologyMap (Cech.CoverRefinement.map U V r M.presheaf) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have he : G.map (HomologicalComplex.homologyMap (BaseCechCoverRefinement.map π U V r M) n) =
      (BaseCechCoverRefinement.homologyIso π M U n).hom ≫
        HomologicalComplex.homologyMap (Cech.CoverRefinement.map U V r M.presheaf) n ≫
        (BaseCechCoverRefinement.homologyIso π M V n).inv := by
    apply (cancel_mono (BaseCechCoverRefinement.homologyIso π M V n).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      BaseCechCoverRefinement.homology_natural π U V r M n
  have : IsIso (G.map (HomologicalComplex.homologyMap (BaseCechCoverRefinement.map π U V r M) n)) := by
    rw [he]
    infer_instance
  exact isIso_of_reflects_iso (HomologicalComplex.homologyMap (BaseCechCoverRefinement.map π U V r M) n) G

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechOpenCoverRefinement.Base

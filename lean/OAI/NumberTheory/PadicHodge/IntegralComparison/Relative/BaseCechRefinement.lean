import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement

/-! # Base Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.BaseCechRefinement

noncomputable section

/-! Quasi-isomorphism of the literal relative Čech total refinement
for affine covers after intersection with the distinguished affine open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open Scheme.Modules

universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  (W : X.Opens) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (O : X.Opens) (hW : IsAffineOpen W)
  (hU : iSup (fun i => W ⊓ U i) = O) (hV : iSup (fun i => W ⊓ V i) = O)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

include O hW hU hV haU haV in
theorem total_quasiIso :
    QuasiIso (RelativeCech.Refinement.map W U V r
      (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).mapHomologicalComplex (.up ℕ)).obj K)) :=
  AugmentedOrdered.CechRefinementTotal.total_quasiIso U V r _
    (fun q => RelativeCech.RefinementQuasiIso.quasiIso W π U V r (K.X q)
      O hW hU hV haU haV)

include O hW hU hV haU haV in
theorem homology_isIso (n : ℕ) :
    IsIso (RelativeCech.Refinement.homology W U V r
      (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).mapHomologicalComplex (.up ℕ)).obj K) n) := by
  let := total_quasiIso π W U V r O hW hU hV haU haV K
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.BaseCechRefinement

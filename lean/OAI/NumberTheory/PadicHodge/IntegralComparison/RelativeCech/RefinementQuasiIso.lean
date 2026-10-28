import OAI.NumberTheory.PadicHodge.IntegralComparison.CechOpenCoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal

/-! # Refinement Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementQuasiIso

noncomputable section

/-! Cover refinement with coefficients restricted by intersection with
a fixed affine open, using the actual nonempty product comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
variable {X : Scheme.{u}} (W : X.Opens)

instance intersection_preserves_product {ι : Type w} [Nonempty ι] (U : ι → X.Opens) :
    PreservesLimit (Discrete.functor U) (Intersections.intersect W) := by
  classical
  let F := Intersections.intersect W
  let a : (∏ᶜ fun i => F.obj (U i)) ⟶ F.obj (∏ᶜ U) := homOfLE (le_inf
    ((leOfHom (Pi.π (fun i => F.obj (U i)) (Classical.choice ‹Nonempty ι›))).trans inf_le_left)
    (leOfHom (Pi.lift (fun i =>
      Pi.π (fun i => F.obj (U i)) i ≫ homOfLE inf_le_right))))
  let : IsIso (piComparison F U) := ⟨⟨a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  exact PreservesProduct.of_iso_comparison F U

variable {S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι κ : Type u} (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (M : X.Modules) [M.IsQuasicoherent] (O : X.Opens)

theorem quasiIso (hW : IsAffineOpen W)
    (hU : iSup (fun i => W ⊓ U i) = O) (hV : iSup (fun i => W ⊓ V i) = O)
    (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i)) :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r
      (Intersections.presheaf W (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M))) := by
  let F := Intersections.intersect W
  let P := AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M
  let : ∀ (n : ℕ) (z : Fin (n + 1) → ι),
      PreservesLimit (Discrete.functor (U ∘ z)) F := fun n z =>
    intersection_preserves_product W (U ∘ z)
  let : ∀ (n : ℕ) (z : Fin (n + 1) → κ),
      PreservesLimit (Discrete.functor (V ∘ z)) F := fun n z =>
    intersection_preserves_product W (V ∘ z)
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (F.obj ∘ U) (F.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover F U V r) P) :=
    CechOpenCoverRefinement.Base.quasiIso π (F.obj ∘ U) (F.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover F U V r) M O hU hV
      (fun i => hW.inf (haU i)) (fun i => hW.inf (haV i))
  change QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (F.op ⋙ P))
  apply (quasiIso_iff_comp_right _ (GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F V P).hom).mp
  rw [Cech.RefinementProductCoordinates.naturality]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementQuasiIso

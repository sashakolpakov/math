import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.BaseCechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductReflect
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward

/-! # Pushforward Relative Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PushforwardRelativeCechRefinement

noncomputable section

/-! Relative Čech refinement for an actual pushed-forward module.
Only the inverse-image covers must cover the same source open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)

def coefficientIso (M : X.Modules) :
    (Opens.map f.base).op ⋙ AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M ≅
      AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M) :=
  NatIso.ofComponents (fun U => AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseModulePresheafPushforwardAppIso f π M U.unop) (by
    intro U V a
    apply ModuleCat.hom_ext
    ext x
    rfl)

variable (W : Y.Opens)

def relativeIso (M : X.Modules) :
    ((RelativeCech.Intersections.intersect W) ⋙ Opens.map f.base).op ⋙
        AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M ≅
      RelativeCech.Intersections.presheaf W
        (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)) :=
  Functor.associator (RelativeCech.Intersections.intersect W).op
      (Opens.map f.base).op (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M) ≪≫
    Functor.isoWhiskerLeft (RelativeCech.Intersections.intersect W).op (coefficientIso f π M)

local instance preimage_limits : PreservesFiniteLimits (Opens.map f.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
  infer_instance

variable [X.IsSeparated] {ι κ : Type u}
  (U : ι → Y.Opens) (V : κ → Y.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (M : X.Modules) [M.IsQuasicoherent] (O : X.Opens)

theorem quasiIso
    (hU : iSup (fun i => f ⁻¹ᵁ (W ⊓ U i)) = O)
    (hV : iSup (fun i => f ⁻¹ᵁ (W ⊓ V i)) = O)
    (haU : ∀ i, IsAffineOpen (f ⁻¹ᵁ (W ⊓ U i)))
    (haV : ∀ i, IsAffineOpen (f ⁻¹ᵁ (W ⊓ V i))) :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r
      (RelativeCech.Intersections.presheaf W
        (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)))) := by
  let F := (RelativeCech.Intersections.intersect W) ⋙ Opens.map f.base
  let P := AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M
  let : ∀ (n : ℕ) (z : Fin (n + 1) → ι),
      PreservesLimit (Discrete.functor (U ∘ z)) F := fun n z => by
    dsimp only [F]
    infer_instance
  let : ∀ (n : ℕ) (z : Fin (n + 1) → κ),
      PreservesLimit (Discrete.functor (V ∘ z)) F := fun n z => by
    dsimp only [F]
    infer_instance
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (F.obj ∘ U) (F.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover F U V r) P) :=
    CechOpenCoverRefinement.Base.quasiIso (f ≫ π) (F.obj ∘ U) (F.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover F U V r) M O hU hV haU haV
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (F.op ⋙ P)) :=
    Cech.RefinementProductReflect.Coordinates.reflect F U V r P
  exact Cech.RefinementProductReflect.Coordinates.coefficients U V r (relativeIso f π W M)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PushforwardRelativeCechRefinement

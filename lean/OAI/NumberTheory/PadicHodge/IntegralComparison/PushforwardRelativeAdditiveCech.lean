import OAI.NumberTheory.PadicHodge.IntegralComparison.PushforwardRelativeCechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CoverRefinementQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.AugmentedCechRefinement

/-! # Pushforward Relative Additive Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PushforwardRelativeAdditiveCech

noncomputable section

/-! The original relative Čech refinement on underlying additive
presheaves of pushed-forward quasicoherent modules. Coverage is required
only on the source scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)

def relativeIso (M : X.Modules) :
    ((RelativeCech.Intersections.intersect W) ⋙ Opens.map f.base).op ⋙ M.presheaf ≅
      RelativeCech.Intersections.presheaf W ((pushforward f).obj M).presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V a; rfl)

local instance preimage_limits : PreservesFiniteLimits (Opens.map f.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
  infer_instance

variable [X.IsSeparated] {ι κ : Type u}
  (U : ι → Y.Opens) (V : κ → Y.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (O : X.Opens)
  (hU : iSup (fun i => f ⁻¹ᵁ (W ⊓ U i)) = O)
  (hV : iSup (fun i => f ⁻¹ᵁ (W ⊓ V i)) = O)
  (haU : ∀ i, IsAffineOpen (f ⁻¹ᵁ (W ⊓ U i)))
  (haV : ∀ i, IsAffineOpen (f ⁻¹ᵁ (W ⊓ V i)))

include O hU hV haU haV in
theorem quasiIso (M : X.Modules) [M.IsQuasicoherent] :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r
      (RelativeCech.Intersections.presheaf W ((pushforward f).obj M).presheaf)) := by
  let F := (RelativeCech.Intersections.intersect W) ⋙ Opens.map f.base
  let : ∀ (n : ℕ) (z : Fin (n + 1) → ι),
      PreservesLimit (Discrete.functor (U ∘ z)) F := fun n z => by
    dsimp only [F]
    infer_instance
  let : ∀ (n : ℕ) (z : Fin (n + 1) → κ),
      PreservesLimit (Discrete.functor (V ∘ z)) F := fun n z => by
    dsimp only [F]
    infer_instance
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (F.obj ∘ U) (F.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover F U V r) M.presheaf) :=
    Open.CoverRefinementQuasiIso.Cech.quasiIso (F.obj ∘ U) (F.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover F U V r) M O hU hV haU haV
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (F.op ⋙ M.presheaf)) :=
    Cech.RefinementProductReflect.Coordinates.reflect F U V r M.presheaf
  exact Cech.RefinementProductReflect.Coordinates.coefficients U V r (relativeIso f W M)

abbrev coefficientComplex (K : CochainComplex X.Modules ℕ) :=
  ((toPresheaf Y).mapHomologicalComplex (.up ℕ)).obj
    (((pushforward f).mapHomologicalComplex (.up ℕ)).obj K)

variable [LinearOrder ι] [LinearOrder κ]
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

include O hU hV haU haV in
theorem total_quasiIso :
    QuasiIso (RelativeCech.Refinement.map W U V r (coefficientComplex f K)) :=
  Additive.AugmentedCechRefinement.total_quasiIso U V r _
    (fun q => quasiIso f W U V r O hU hV haU haV (K.X q))

include O hU hV haU haV in
theorem homology_isIso (n : ℕ) :
    IsIso (RelativeCech.Refinement.homology W U V r (coefficientComplex f K) n) := by
  let := total_quasiIso f W U V r O hU hV haU haV K
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PushforwardRelativeAdditiveCech

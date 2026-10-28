import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReciprocalFrameTensorIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

/-! # Reciprocal Frame Pairing Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual reciprocal-frame tensor pairing multiplies the two frame coordinates on every subordinate open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (F : CompatibleSheaf.CompatibleSheafFrames D.reciprocal N)
variable (hU : ∀ x : X, ∃ i, x ∈ U i)

def CompatibleSheaf.CompatibleSheafFrames.reciprocalPairing : Bilinear.Sheaves.SheafBilinearMap M N (Line.Bundles.structureModule X) :=
  Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (Line.Bundles.structureModule X) (E.reciprocalTensorIso F hU).hom

theorem CompatibleSheaf.CompatibleSheafFrames.reciprocalPairing_app (V : X.Opens) (i : ι) (hi : V ≤ U i)
    (x : Γ(M, V)) (y : Γ(N, V)) :
    (E.reciprocalPairing F hU).app V x y =
      (E.frame V i hi).symm x * (F.frame V i hi).symm y := by
  let W : Module.OpenMapGluing.SubordinateOpenIndex U := ⟨V, i, hi⟩
  let z : Γ(M, V) ⊗[Γ(X, V)] Γ(N, V) := x ⊗ₜ[Γ(X, V)] y
  have he := (E.reciprocalTensorBasisMap F).extend_app
    (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU) W z
  have ha : Tensor.ProductSheaf.tensorModuleHomEquiv M N (Line.Bundles.structureModule X) (E.reciprocalTensorIso F hU).hom =
      (E.reciprocalTensorBasisMap F).extend (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU) := by
    exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).apply_symm_apply _
  change (Tensor.ProductSheaf.tensorModuleHomEquiv M N (Line.Bundles.structureModule X) (E.reciprocalTensorIso F hU).hom).app
    (.op V) (x ⊗ₜ[Γ(X, V)] y) = _
  rw [ha]
  exact he.trans ((congrArg (fun e : Γ(M, V) ⊗[Γ(X, V)] Γ(N, V) ≃ₗ[Γ(X, V)] Γ(X, V) =>
      e (x ⊗ₜ[Γ(X, V)] y)) (E.reciprocalTensorCoordinate_independent F V
        (Classical.choose W.property) i (Classical.choose_spec W.property) hi)).trans
          (E.reciprocalTensorCoordinate_tmul F V i hi x y))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.FrameRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSheafificationIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

/-! # Frame Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual tensor power of a sheaf with compatible rank-one frames is the sheaf with the powered frame cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (d : ℕ) (F : CompatibleSheaf.CompatibleSheafFrames (D.power d) N)

def CompatibleSheaf.CompatibleSheafFrames.tensorBasisMap : PresheafModuleBasisMaps.PresheafModuleBasisMap (Module.OpenMapGluing.subordinateOpenBasis U) (TensorPower.Presheaf.tensorPowerPresheaf M d) N where
  app V := (E.tensorComparison d F V.val (Classical.choose V.property) (Classical.choose_spec V.property)).toLinearMap
  naturality V W h x := E.tensorComparison_restrict d F W.val V.val h
    (Classical.choose V.property) (Classical.choose W.property)
    (Classical.choose_spec V.property) (Classical.choose_spec W.property) x

def CompatibleSheaf.CompatibleSheafFrames.tensorPowerIso (hU : ∀ x : X, ∃ i, x ∈ U i) : TensorPower.PowerSheaf.tensorPowerModule M d ≅ N :=
  (E.tensorBasisMap d F).sheafificationIso (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU)
    (fun V => (E.tensorComparison d F V.val (Classical.choose V.property) (Classical.choose_spec V.property)).bijective)

def TensorPower.FrameRecognition.openFrameTensorPowerIso {κ : Type u} {V : κ → X.Opens} (C : OpenFrame.Transitions.OpenFrameTransitions V)
    (hV : ∀ x : X, ∃ i, x ∈ V i) (k : ℕ) :
    TensorPower.PowerSheaf.tensorPowerModule (OpenFrame.ModuleSheaf.openFrameModuleSheaf C) k ≅ OpenFrame.ModuleSheaf.openFrameModuleSheaf (C.power k) :=
  (ConstructedCompatibleFrames.openFrameSheafFrames C).tensorPowerIso k (ConstructedCompatibleFrames.openFrameSheafFrames (C.power k)) hV

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleFrameComparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

/-! # Frame Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Compatible actual local frames with the same cocycle determine a global sheaf isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (F : CompatibleSheaf.CompatibleSheafFrames D N)

def CompatibleSheaf.CompatibleSheafFrames.comparisonBasisMap : Module.MapBasisExtension.ModuleBasisMap (Module.OpenMapGluing.subordinateOpenBasis U) M N where
  app V := (E.comparison F V.val (Classical.choose V.property) (Classical.choose_spec V.property)).toLinearMap
  naturality V W h x := E.comparison_restrict F W.val V.val h
    (Classical.choose V.property) (Classical.choose W.property)
    (Classical.choose_spec V.property) (Classical.choose_spec W.property) x

def CompatibleSheaf.CompatibleSheafFrames.iso (hU : ∀ x : X, ∃ i, x ∈ U i) : M ≅ N :=
  (E.comparisonBasisMap F).extendIso (Module.OpenMapGluing.subordinateOpenBasis U) (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU)
    (fun V => (E.comparison F V.val (Classical.choose V.property) (Classical.choose_spec V.property)).bijective)

theorem CompatibleSheaf.CompatibleSheafFrames.iso_app (hU : ∀ x : X, ∃ i, x ∈ U i)
    (V : X.Opens) (i : ι) (hi : V ≤ U i) (x : Γ(M, V)) :
    (E.iso F hU).hom.app V x = E.comparison F V i hi x := by
  let W : Module.OpenMapGluing.SubordinateOpenIndex U := ⟨V, i, hi⟩
  have he := (E.comparisonBasisMap F).extend_app (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU) W x
  exact he.trans (congrArg (fun e : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) => e x)
    (E.comparison_independent F V (Classical.choose W.property) i (Classical.choose_spec W.property) hi))

def Sheaf.FrameRecognition.openFrameSheafRecognitionIso {κ : Type u} {V : κ → X.Opens} (C : OpenFrame.Transitions.OpenFrameTransitions V)
    {P : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames C P) (hV : ∀ x : X, ∃ i, x ∈ V i) :
    OpenFrame.ModuleSheaf.openFrameModuleSheaf C ≅ P :=
  (ConstructedCompatibleFrames.openFrameSheafFrames C).iso E hV

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

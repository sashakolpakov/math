import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameCoefficientMaps

/-! # Frame Coefficient Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameCoefficientGluing

noncomputable section

/-! Compatible frame coefficients give an actual global morphism of module sheaves, with its section values verified. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M)
variable (t : ∀ i, Γ(N, U i)) (ht : FrameCoefficientMaps.FrameMorphismCompatible (D := D) t)

def frameCoefficientBasisMap : Module.MapBasisExtension.ModuleBasisMap (Module.OpenMapGluing.subordinateOpenBasis U) M N where
  app V := FrameCoefficientMaps.frameCoefficientMap E t V.val (Classical.choose V.property) (Classical.choose_spec V.property)
  naturality V W h x := by
    have hi := Classical.choose_spec V.property
    have hj := Classical.choose_spec W.property
    change FrameCoefficientMaps.frameCoefficientMap E t V.val (Classical.choose V.property) hi
      (M.presheaf.map (homOfLE h).op x) = _
    rw [FrameCoefficientMaps.frameCoefficientMap_independent E t ht V.val
      (Classical.choose V.property) (Classical.choose W.property) hi (h.trans hj)]
    exact FrameCoefficientMaps.frameCoefficientMap_restrict E t W.val V.val h (Classical.choose W.property) hj x

def frameCoefficientMorphism (hU : ∀ x : X, ∃ i, x ∈ U i) : M ⟶ N :=
  (frameCoefficientBasisMap E t ht).extend (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU)

theorem frameCoefficientMorphism_app (hU : ∀ x : X, ∃ i, x ∈ U i)
    (V : X.Opens) (i : ι) (hi : V ≤ U i) (x : Γ(M, V)) :
    (frameCoefficientMorphism E t ht hU).app V x = FrameCoefficientMaps.frameCoefficientMap E t V i hi x := by
  let W : Module.OpenMapGluing.SubordinateOpenIndex U := ⟨V, i, hi⟩
  exact ((frameCoefficientBasisMap E t ht).extend_app
    (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU) W x).trans
      (LinearMap.congr_fun (FrameCoefficientMaps.frameCoefficientMap_independent E t ht V
        (Classical.choose W.property) i (Classical.choose_spec W.property) hi) x)

theorem frameCoefficientMorphism_frame (hU : ∀ x : X, ∃ i, x ∈ U i) (i : ι) :
    (frameCoefficientMorphism E t ht hU).app (U i) (E.frame (U i) i le_rfl 1) = t i := by
  rw [frameCoefficientMorphism_app E t ht hU (U i) i le_rfl]
  change (E.frame (U i) i le_rfl).symm (E.frame (U i) i le_rfl 1) •
    N.presheaf.map (homOfLE (show U i ≤ U i from le_rfl)).op (t i) = t i
  simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameCoefficientGluing

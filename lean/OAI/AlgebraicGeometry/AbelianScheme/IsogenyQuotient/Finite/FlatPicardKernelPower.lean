import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalNormSection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes

/-! # Flat Picard Kernel Power -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatPicardKernelPower.Construction

noncomputable section

/-! The actual finite-flat norm turns a frame of a pulled-back line
into a frame of its degree power, over an unrestricted base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames

universe u
variable {X Y : Scheme.{u}} (q : X ⟶ Y)
  [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (d : ℕ) (hdegree : ∀ y : Y, q.finrank y = d)

include hdegree in
theorem finiteFlatNormSection_isIso_of_frame
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) [IsIso s] :
    IsIso (GlobalNormSection.Construction.finiteFlatNormSection q L d hdegree s) := by
  apply (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
  ext y
  change y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (GlobalNormSection.Construction.finiteFlatNormSection q L d hdegree s) ↔ True
  rw [GlobalNormSection.Construction.finiteFlatNormSection_mem_nonvanishing]
  exact iff_true_intro (fun x _ => by rw [AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso s]; trivial)

include hdegree in
theorem finiteFlatPullbackTrivial_tensorPower_trivial
    (e : (L.pullback q).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    Nonempty ((L.tensorPower d).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) := by
  have : IsIso (GlobalNormSection.Construction.finiteFlatNormSection q L d hdegree e.inv) :=
    finiteFlatNormSection_isIso_of_frame q L d hdegree e.inv
  exact ⟨(asIso (GlobalNormSection.Construction.finiteFlatNormSection q L d hdegree e.inv)).symm⟩

include hdegree in
theorem finiteFlatPullbackKernel_class_pow
    (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ d = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass Y := by
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf_tensorPower]
  exact Quotient.sound (finiteFlatPullbackTrivial_tensorPower_trivial q L d hdegree
    (Classical.choice (Quotient.exact hL)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatPicardKernelPower.Construction

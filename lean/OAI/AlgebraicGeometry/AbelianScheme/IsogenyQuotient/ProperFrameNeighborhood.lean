import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalTraceBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiberContainment
import Mathlib.AlgebraicGeometry.Fiber

/-! # Proper Frame Neighborhood -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperFrameNeighborhood.Construction

noncomputable section

/-! A section which is a frame on one fiber of a proper family is a
frame over a neighborhood of that fiber. The neighborhood is the
complement of the actual proper image of its vanishing locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiberContainment

universe u
variable {X S : Scheme.{u}} (p : X ⟶ S) [UniversallyClosed p]
  {L : X.Modules} (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L)

def sectionFrameNeighborhood : S.Opens := AbelianModuli.HilbertConstruction.Proper.FiberContainment.properFiberContainmentOpen p (𝟙 X) (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z)

theorem mem_sectionFrameNeighborhood_iff (s : S) :
    s ∈ sectionFrameNeighborhood p z ↔ ∀ x : X, p x = s → x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z :=
  AbelianModuli.HilbertConstruction.Proper.FiberContainment.mem_properFiberContainmentOpen_iff p (𝟙 X) (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) s

theorem sectionFrameNeighborhood_isIso :
    IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (p ⁻¹ᵁ sectionFrameNeighborhood p z).ι z) := by
  apply (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
  rw [AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback]
  ext x
  exact iff_true_intro (AbelianModuli.HilbertConstruction.Proper.FiberContainment.properFiberContainmentOpen_preimage_le p (𝟙 X) (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) x.property)

theorem mem_sectionFrameNeighborhood_of_fiber_isIso (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (w : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M.sheaf) (s : S)
    [IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (p.fiberι s) w)] : s ∈ sectionFrameNeighborhood p w := by
  apply (mem_sectionFrameNeighborhood_iff p w s).mpr
  intro x hx
  have hr : x ∈ Set.range (p.fiberι s) := (p.range_fiberι s).symm ▸ hx
  obtain ⟨y, rfl⟩ := hr
  have h := AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (p.fiberι s) w)
  rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange (p.fiberι s) M w] at h
  exact (congrArg (fun U : (p.fiber s).Opens => y ∈ U) h).mpr trivial

theorem mem_sectionFrameNeighborhood_of_baseChange_isIso
    (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (w : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M.sheaf)
    {T : Scheme.{u}} (t : T ⟶ S) (s : S) (hs : s ∈ Set.range t)
    [IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst p t) w)] : s ∈ sectionFrameNeighborhood p w := by
  apply (mem_sectionFrameNeighborhood_iff p w s).mpr
  intro x hx
  have hp : p x ∈ Set.range t := hx.symm ▸ hs
  have hr : x ∈ Set.range (pullback.fst p t) :=
    (Scheme.Pullback.range_fst (f := p) (g := t)).symm ▸ hp
  obtain ⟨y, rfl⟩ := hr
  have h := AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst p t) w)
  rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange (pullback.fst p t) M w] at h
  exact (congrArg (fun U : (pullback p t).Opens => y ∈ U) h).mpr trivial

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperFrameNeighborhood.Construction

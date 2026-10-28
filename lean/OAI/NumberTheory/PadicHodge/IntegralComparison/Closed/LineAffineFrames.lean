import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FramePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Line Affine Frames -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.LineAffineFrames

noncomputable section

/-! A line bundle on a surjective closed subscheme has local frames
on inverse images of an actual affine cover of the ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f] [Surjective f]
  (L : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)

structure Frame (x : X) where
  openSubset : X.Opens
  affine : IsAffineOpen openSubset
  mem : x ∈ openSubset
  sourceIndex : Y
  subordinate : f ⁻¹ᵁ openSubset ≤ L.frameOpen sourceIndex

theorem nonempty_frame (x : X) : Nonempty (Frame f L x) := by
  obtain ⟨y, rfl⟩ := f.surjective x
  have hf : IsHomeomorph f :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨f.isClosedEmbedding.isEmbedding, f.surjective⟩
  let V : X.Opens := ⟨f '' (L.frameOpen y : Set Y), hf.isOpenMap _ (L.frameOpen y).isOpen⟩
  have hy : f y ∈ V := ⟨y, L.mem_frameOpen y, rfl⟩
  obtain ⟨U, hU, hyU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hy
  refine ⟨⟨U, hU, hyU, y, ?_⟩⟩
  intro z hz
  obtain ⟨w, hw, hwz⟩ := hUV hz
  have he : w = z := f.isClosedEmbedding.injective hwz
  exact he ▸ hw

def frame (x : X) : Frame f L x := Classical.choice (nonempty_frame f L x)

abbrev opens (x : X) : X.Opens := (LineAffineFrames.frame f L x).openSubset

theorem affine (x : X) : IsAffineOpen (opens f L x) := (LineAffineFrames.frame f L x).affine

theorem covers (x : X) : ∃ i, x ∈ opens f L i := ⟨x, (LineAffineFrames.frame f L x).mem⟩

theorem preimage_covers (y : Y) : ∃ i, y ∈ f ⁻¹ᵁ opens f L i := covers f L (f y)

def naturalFrames : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalSheaf.NaturalSheafFrames (fun x => f ⁻¹ᵁ opens f L x) L.sheaf where
  frame V x h := L.naturalFrames.frame V (LineAffineFrames.frame f L x).sourceIndex
    (h.trans (LineAffineFrames.frame f L x).subordinate)
  restrict V W h x hx a := L.naturalFrames.restrict V W h (LineAffineFrames.frame f L x).sourceIndex
    (hx.trans (LineAffineFrames.frame f L x).subordinate) a

def sourceIso : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf.openFrameModuleSheaf (LineAffineFrames.naturalFrames f L).transitions ≅ L.sheaf :=
  OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameRecognition.openFrameSheafRecognitionIso (LineAffineFrames.naturalFrames f L).transitions
    (LineAffineFrames.naturalFrames f L).compatible (preimage_covers f L)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.LineAffineFrames

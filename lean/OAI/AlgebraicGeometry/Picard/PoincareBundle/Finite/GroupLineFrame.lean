import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AffineLineFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation

/-! # Group Line Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupLineFrame

noncomputable section

/-! Global frames for actual line bundles on finite commutative group schemes over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

/-- A global frame on an isomorphic scheme transports to a frame of the original line. -/
def frame_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (L : Line.Bundles.LineBundle Y)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback e.hom).obj L.sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ L.sheaf :=
  FrameRatioPullback.pullFrame e.inv s ≪≫
    (Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Y).app L.sheaf

/-- Finiteness supplies coordinates and semilocal Picard triviality supplies the actual frame. -/
theorem exists_frame (k : Type u) [Field k] (H : Over (Spec (.of k)))
    [GrpObj H] [IsCommMonObj H] [IsFinite H.hom] (L : Line.Bundles.LineBundle H.left) :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left) := by
  obtain ⟨R, hf, _, ⟨e⟩⟩ := Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k (Grp.mk H)
  have : Module.Finite k R := hf
  let i : ((Spec (.of R)).asOver (Spec (.of k))) ≅ H := (Grp.forget _).mapIso e
  let j : Spec (.of R) ≅ H.left := (Over.forget (Spec (.of k))).mapIso i
  obtain ⟨s⟩ := AffineLineFrame.exists_frame k R (L.pullback j.hom)
  exact ⟨(frame_of_iso j L s.symm).symm⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupLineFrame

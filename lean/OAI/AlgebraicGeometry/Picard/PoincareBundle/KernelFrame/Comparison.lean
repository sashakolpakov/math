import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TransverseFrames

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Comparison

noncomputable section

/-!
# Explicit actual frames under coordinate exchange and symmetry
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

variable {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [GrpObj B]
  {p p' : E ⟶ A} {r r' : E ⟶ X} (f : A ⟶ B) [IsMonHom f]
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L) (F : FiberwiseMultiplication.KernelFrames p r L f D)

/-- Changing equal coordinate maps retains the same actual kernel frame. -/
theorem congrCoordinates_frame (hp : p = p') (hr : r = r') {T : Over S}
    (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ E) (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p') :
    (Kernel.FramesPullback.congrCoordinates f L D F hp hr).frame k a ha =
      F.frame k a (ha.trans (congrArg (fun q => a ≫ q) hp.symm)) := by
  cases hp
  cases hr
  rfl

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle (A ⊗ A).left)
  (D : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L) (F : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f D)

omit [GrpObj A] [IsMonHom f] in
/-- A second-coordinate kernel point becomes a first-coordinate kernel point after actual exchange. -/
theorem exchanged_kernel {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ A)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ snd A A) :
    k ≫ Kernel.Scheme.kernelInclusion f = (a ≫ (β_ A A).hom) ≫ fst A A := by
  rw [Category.assoc, braiding_hom_fst]
  exact ha

/-- The exchanged frame is the original frame carried through the canonical fiber comparison. -/
theorem exchanged_frame {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ A)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ snd A A) :
    (Symmetric.MultiplicativeFrames.exchangedFrames L D f F).frame k a ha =
      Pulled.LineSection.transportFrame (β_ A A).hom L a (a ≫ (β_ A A).hom) rfl
        (F.frame k (a ≫ (β_ A A).hom) (exchanged_kernel f k a ha)) := by
  unfold Symmetric.MultiplicativeFrames.exchangedFrames
  rw [congrCoordinates_frame]
  rfl

/-- The second frame is the exchanged first frame followed by the actual symmetry isomorphism. -/
theorem second_frame
    (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)
    {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ A)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ snd A A) :
    (Symmetric.MultiplicativeFrames.secondFrames L D e f F).frame k a ha =
      Line.FiberIsomorphisms.transportFrame (L.pullback (β_ A A).hom.left) L e a
        (Pulled.LineSection.transportFrame (β_ A A).hom L a (a ≫ (β_ A A).hom) rfl
          (F.frame k (a ≫ (β_ A A).hom) (exchanged_kernel f k a ha))) := by
  change Line.FiberIsomorphisms.transportFrame (L.pullback (β_ A A).hom.left) L e a
    ((Symmetric.MultiplicativeFrames.exchangedFrames L D f F).frame k a ha) = _
  rw [exchanged_frame]

/-- Identifying the transported product with the given product changes no actual frame. -/
theorem compatible_second_frame (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L)
    (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)
    (hv : Symmetric.MultiplicativeFrames.secondMultiplication L D e = Dv) {T : Over S}
    (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ A) (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ snd A A) :
    (Symmetric.TransverseFrames.secondFramesOfCompatible L D Dv e f F hv).frame k a ha =
      (Symmetric.MultiplicativeFrames.secondFrames L D e f F).frame k a ha := by
  cases hv
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Comparison

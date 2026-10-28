import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.IntrinsicScalars
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalDescentCharacter

/-! # Kernel Pairing Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.KernelPairingCharacter

noncomputable section

/-! The actual recovered quotient line has native character equal to the inverse original kernel pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  [IsCommMonObj X] (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The actual ordinary descent of the first-kernel parameter family. -/
def datum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g).left) :=
  Vertical.KernelDescent.ordinaryDatum g (L.pullback (KernelFrame.Global.universalPoint f).left)
    (Vertical.ParameterKernelFrames.multiplication (Kernel.Scheme.kernelInclusion f) L Dv) (Vertical.ParameterKernelFrames.frames (Kernel.Scheme.kernelInclusion f) g L Dv Kv)

variable (M : Line.Bundles.LineBundle (Kernel.Scheme.kernelObject f ⊗ Y).left)
  (r : Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks)
    (f := fun (_ : PUnit.{1}) => (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g).left) M.sheaf ≅ datum f g L Dv Kv)

/-- Recovery and the canonical first-kernel frame give an actual trivialization on the cover. -/
def frame : (Scheme.Modules.pullback (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g).left).obj M.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Kernel.Scheme.kernelObject f ⊗ X).left :=
  IntrinsicScalars.Intrinsic.frame (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g).left M.sheaf (datum f g L Dv Kv) r
    (KernelFrame.Global.globalFrame f L Dh Kh).symm

variable (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include ht

/-- The recovered line's full native translation character is exactly the inverse pairing value. -/
theorem scalar_translation {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (z w : T ⟶ X) (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ Kernel.Scheme.kernelObject f ⊗ Y)
    (hz : lift k z ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g) = q) (hw : lift k w ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g).left M.sheaf)
      (frame f g L Dh Dv Kh Kv M r) q.left (lift k z).left (lift k w).left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
      (ConcreteKernelPairing.Concrete.value f g L Dh Dv Kh Kv k l)⁻¹.val := by
  have hs := IntrinsicScalars.Intrinsic.scalar_eq (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ g).left M.sheaf
    (datum f g L Dv Kv) r (KernelFrame.Global.globalFrame f L Dh Kh).symm q.left (lift k z).left (lift k w).left
    (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw)
  exact hs.trans (Kernel.GlobalDescentCharacter.scalar_translation f g L Dh Dv Kh Kv ht k l z w h q hz hw)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.KernelPairingCharacter

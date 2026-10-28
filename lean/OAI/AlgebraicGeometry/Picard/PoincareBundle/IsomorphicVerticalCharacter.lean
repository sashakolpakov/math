import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicVerticalDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicKernelFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Ext

/-! # Isomorphic Vertical Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicVerticalCharacter

noncomputable section

/-! A product-compatible line isomorphism identifies the actual native characters of any transverse kernel-frame presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

variable {k : Type u} [Field k] {A X Y : Over (Spec (.of k))}
  [GrpObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g] [IsAffine (Kernel.Scheme.kernelObject g).left]
  (L M : Line.Bundles.LineBundle (A ⊗ X).left) (e : L.sheaf ≅ M.sheaf)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Eh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) M) (Ev : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) M)
  (hh : FiberwiseMultiplicationIso.transportMultiplication (fst A X) (snd A X) L M e Dh = Eh)
  (hv : FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv = Ev)
  (K : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv) (J : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) M g Ev)
  (hK : Kernel.FramesTransverseTransport.Transverse g K Dh) (hJ : Kernel.FramesTransverseTransport.Transverse g J Eh)

include hh hv hK hJ

/-- The actual native gluing maps agree through the product-compatible line isomorphism, without requiring a global frame. -/
theorem hom_compatible {T : Over (Spec (.of k))} (q : T ⟶ A ⊗ Y) (x y : T ⟶ A ⊗ X)
    (hx : x ≫ (𝟙 A ⊗ₘ g) = q) (hy : y ≫ (𝟙 A ⊗ₘ g) = q) :
    (Scheme.Modules.pullback x.left).map e.hom ≫ (Vertical.KernelDescent.nativeDatum g M Ev J).hom
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Vertical.KernelDescent.nativeDatum g L Dv K).hom q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫ (Scheme.Modules.pullback y.left).map e.hom := by
  subst Eh
  subst Ev
  have hj : FiberwiseMultiplicationIso.transportKernelFrames (snd A X) (fst A X) L M e Dv g K = J := by
    apply KernelFrame.Ext.ext
    intro U z a ha
    exact IsomorphicKernelFrames.vertical_frame g L M e Dh Dv
      (FiberwiseMultiplicationIso.transportMultiplication (fst A X) (snd A X) L M e Dh)
      (FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e Dv) rfl rfl K J hK hJ z a ha
  rw [← hj]
  exact IsomorphicVerticalDescent.hom_compatible g L M e Dv K q x y hx hy

/-- Proper connected geometry removes the choice of transverse kernel frames from the native character comparison. -/
theorem scalar_eq (s : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ X).left)
    {T : Over (Spec (.of k))} (q : T ⟶ A ⊗ Y) (x y : T ⟶ A ⊗ X)
    (hx : x ≫ (𝟙 A ⊗ₘ g) = q) (hy : y ≫ (𝟙 A ⊗ₘ g) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Vertical.KernelDescent.nativeDatum g M Ev J) (e.symm ≪≫ s)
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Vertical.KernelDescent.nativeDatum g L Dv K) s
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) :=
  FramedDescentIso.scalar_eq (Vertical.KernelDescent.nativeDatum g L Dv K) (Vertical.KernelDescent.nativeDatum g M Ev J) e s
    q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)
    (hom_compatible g L M e Dh Dv Eh Ev hh hv K J hK hJ q x y hx hy)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicVerticalCharacter

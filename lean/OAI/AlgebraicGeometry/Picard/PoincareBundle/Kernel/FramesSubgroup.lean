import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

/-! # Frames Subgroup -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesSubgroup

noncomputable section

/-! The complete natural kernel-frame system restricts to every actual subgroup-scheme inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {E A B C X : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
  (i : Kernel.Scheme.kernelObject f ⟶ Kernel.Scheme.kernelObject g) [IsMonHom i]
  (hi : i ≫ Kernel.Scheme.kernelInclusion g = Kernel.Scheme.kernelInclusion f)
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L)
  (K : FiberwiseMultiplication.KernelFrames p r L g D)

include hi in
omit [GrpObj A] [IsMonHom f] [IsMonHom g] [IsMonHom i] in
/-- The included kernel point retains the original ambient group coordinate. -/
theorem imageKernel {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ E)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) : (k ≫ i) ≫ Kernel.Scheme.kernelInclusion g = a ≫ p := by
  rw [Category.assoc, hi, ha]

/-- Restriction retains all actual frame, product, unit, and naturality laws. -/
def restrict : FiberwiseMultiplication.KernelFrames p r L f D where
  frame := fun {_T} k a ha => K.frame (k ≫ i) a (imageKernel p f g i hi k a ha)
  unit := fun {T} a ha hk => by
    simp only [MonObj.one_comp]
    exact K.unit a ha _
  multiplicative := fun {_T} k l t hkt a b c ha hb hc hab U =>
    K.multiplicative (k ≫ i) (l ≫ i) (t ≫ i)
      ((MonObj.mul_comp k l i).symm.trans (congrArg (fun z => z ≫ i) hkt)) a b c
      (imageKernel p f g i hi k a ha) (imageKernel p f g i hi l b hb) (imageKernel p f g i hi t c hc) hab U
  natural := fun {_T _U} u k k' huk a a' ha ha' hua =>
    K.natural u (k ≫ i) (k' ≫ i) ((Category.assoc u k i).symm.trans (congrArg (fun z => z ≫ i) huk))
      a a' (imageKernel p f g i hi k a ha) (imageKernel p f g i hi k' a' ha') hua

variable [GrpObj X] (Dv : FiberwiseMultiplication.Multiplication r p L)
  (ht : FramesTransverseTransport.Transverse g K Dv)

include ht

/-- The actual subgroup restriction preserves transversality with the opposite product. -/
theorem transverse : FramesTransverseTransport.Transverse f (restrict p r f g i hi L D K) Dv := by
  intro T k a b c ha hb hc h U
  exact ht T (k ≫ i) a b c (imageKernel p f g i hi k a ha) (imageKernel p f g i hi k b hb)
    (imageKernel p f g i hi k c hc) h U

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesSubgroup

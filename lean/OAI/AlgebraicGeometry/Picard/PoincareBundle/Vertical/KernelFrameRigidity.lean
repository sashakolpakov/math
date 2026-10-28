import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseFrameUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.FamilyFrameUniqueness
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullSectionEquality

/-! # Kernel Frame Rigidity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelFrameRigidity

noncomputable section

/-! Proper connected geometry uniquely determines the second-coordinate kernel frames on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

section Global

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g] (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (K : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The actual universal second-coordinate subgroup point, with the kernel parameter first. -/
def universalPoint : Kernel.Scheme.kernelObject g ⊗ A ⟶ A ⊗ X :=
  lift (snd (Kernel.Scheme.kernelObject g) A) (fst (Kernel.Scheme.kernelObject g) A ≫ Kernel.Scheme.kernelInclusion g)

omit [GrpObj X] [IsMonHom g] in
/-- The universal point has exactly the represented second kernel coordinate. -/
theorem universalPoint_snd : fst (Kernel.Scheme.kernelObject g) A ≫ Kernel.Scheme.kernelInclusion g = universalPoint g ≫ snd A X := by
  simp [universalPoint]

/-- The natural frame system defines a single actual frame on the full subgroup product. -/
def globalFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Kernel.Scheme.kernelObject g ⊗ A).left ≅ Line.Fibers.fiber L (universalPoint g) :=
  K.frame (fst (Kernel.Scheme.kernelObject g) A) (universalPoint g) (universalPoint_snd g)

/-- All second-coordinate frames are actual pullbacks of that universal frame. -/
theorem globalFrame_natural {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject g) (a : T ⟶ A ⊗ X)
    (ha : k ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A X) :
    Line.Fibers.pullSection L (lift k (a ≫ fst A X)) (universalPoint g) a
      (by ext <;> simp [universalPoint, ha]) (globalFrame g L Dv K).hom = (K.frame k a ha).hom :=
  K.natural (lift k (a ≫ fst A X)) (fst (Kernel.Scheme.kernelObject g) A) k (by simp)
    (universalPoint g) a (universalPoint_snd g) ha (by ext <;> simp [universalPoint, ha])

variable [GrpObj A] (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
  (ht : Kernel.FramesTransverseTransport.Transverse g K Dh)

include ht in
/-- Transversality fixes the universal frame on the zero section of the proper factor. -/
theorem globalFrame_zero :
    Line.Fibers.pullSection L (lift (𝟙 (Kernel.Scheme.kernelObject g)) (1 : Kernel.Scheme.kernelObject g ⟶ A)) (universalPoint g)
      (lift (1 : Kernel.Scheme.kernelObject g ⟶ A) (Kernel.Scheme.kernelInclusion g)) (by simp [universalPoint])
      (globalFrame g L Dv K).hom =
        (Dh.unitFrame (lift (1 : Kernel.Scheme.kernelObject g ⟶ A) (Kernel.Scheme.kernelInclusion g)) (by simp)).hom := by
  have hn := K.natural (lift (𝟙 (Kernel.Scheme.kernelObject g)) (1 : Kernel.Scheme.kernelObject g ⟶ A))
    (fst (Kernel.Scheme.kernelObject g) A) (𝟙 (Kernel.Scheme.kernelObject g)) (by simp)
    (universalPoint g) (lift (1 : Kernel.Scheme.kernelObject g ⟶ A) (Kernel.Scheme.kernelInclusion g))
    (universalPoint_snd g) (by simp) (by simp [universalPoint])
  exact hn.trans (congrArg Iso.hom
    (TransverseFrameUnits.vertical_frame_eq_horizontal_unit g L Dh Dv K ht
      (𝟙 (Kernel.Scheme.kernelObject g)) (lift (1 : Kernel.Scheme.kernelObject g ⟶ A) (Kernel.Scheme.kernelInclusion g)) (by simp) (by simp)))

end Global

variable {k : Type u} [Field k] {A X Y : Over (Spec (.of k))}
  [GrpObj A] [GrpObj X] [GrpObj Y]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (g : X ⟶ Y) [IsMonHom g] [IsAffine (Kernel.Scheme.kernelObject g).left]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (K J : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hK : Kernel.FramesTransverseTransport.Transverse g K Dh)
  (hJ : Kernel.FramesTransverseTransport.Transverse g J Dh)

include hK hJ

/-- The proper-family zero normalization determines the actual universal vertical frame. -/
theorem globalFrame_eq : globalFrame g L Dv K = globalFrame g L Dv J := by
  apply Affine.FamilyFrameUniqueness.Family.iso_eq_of_zero A (Kernel.Scheme.kernelObject g)
    (Line.Bundles.LineBundle.trivial (Kernel.Scheme.kernelObject g ⊗ A).left) (L.pullback (universalPoint g).left)
  apply PullSectionEquality.pullback_map_eq L
    (lift (𝟙 (Kernel.Scheme.kernelObject g)) (1 : Kernel.Scheme.kernelObject g ⟶ A)) (universalPoint g)
    (lift (1 : Kernel.Scheme.kernelObject g ⟶ A) (Kernel.Scheme.kernelInclusion g)) (by simp [universalPoint])
  exact (globalFrame_zero g L Dv K Dh hK).trans (globalFrame_zero g L Dv J Dh hJ).symm

/-- Every actual second-coordinate kernel frame is fixed by naturality and transversality. -/
theorem frame_eq {T : Over (Spec (.of k))} (x : T ⟶ Kernel.Scheme.kernelObject g) (a : T ⟶ A ⊗ X)
    (ha : x ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A X) : K.frame x a ha = J.frame x a ha := by
  apply Iso.ext
  rw [← globalFrame_natural g L Dv K x a ha, ← globalFrame_natural g L Dv J x a ha,
    globalFrame_eq g L Dh Dv K J hK hJ]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelFrameRigidity

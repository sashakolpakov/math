import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransverseNeutralPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationFixedMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseInterchange

/-! # Transverse Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

noncomputable section

/-!
# Construct transverse multiplicativity of the canonical Poincare kernel frames

Only the genuine two Poincare products and their interchange law are used. The first kernel
frame is the one already constructed from scheme-theoretic annihilation; no transverse
kernel-frame condition is supplied as input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {A B Z X : Over S} [GrpObj A] [GrpObj B] [GrpObj Z] [GrpObj X]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z X) (snd Z X) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z X) (fst Z X) P)

/-- The actual vertical product pulled back to the image-coordinate presentation. -/
def imageVertical : FiberwiseMultiplication.Multiplication (snd A X) (fst A X ≫ φ) (FirstBiextensionFactor.familyLine P φ) :=
  MultiplicationCoordinates.congrCoordinates
    (FiberwiseMultiplicationPullback.pullbackMultiplication (snd Z X) (fst Z X) (φ ⊗ₘ 𝟙 X) P Dv)
    ((tensorHom_snd φ (𝟙 X)).trans (Category.comp_id (snd A X))) (tensorHom_fst φ (𝟙 X))

/-- Refining the fixed coordinate gives the actual vertical multiplication on the pulled line. -/
def sourceVertical : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) (FirstBiextensionFactor.familyLine P φ) :=
  MultiplicationFixedMap.restrictFixed (snd A X) (fst A X) φ (FirstBiextensionFactor.familyLine P φ) (imageVertical φ P Dv)

variable (hi : Biextension.Compatibility.Interchange P Dh Dv)

include hi in
/-- Both constructed products on the Poincare pullback satisfy genuine biextension interchange. -/
theorem source_interchange : Biextension.Compatibility.Interchange (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (sourceVertical φ P Dv) := by
  apply FiberwiseInterchange.restrictCoordinate
  apply FiberwiseInterchange.congrCoordinates
  exact FiberwiseInterchange.pullback (φ ⊗ₘ 𝟙 X) Dh Dv hi

include hi in
omit [GrpObj A] [IsMonHom φ] in
/-- Interchange of the original Poincare products proves the pulled neutral-frame transverse law. -/
theorem image_transverse :
    TransverseNeutralPullback.TransverseUnits (Pulled.KernelFrames.Poincare.imageMultiplication φ P Dh) (imageVertical φ P Dv) := by
  apply TransverseNeutralPullback.congrCoordinates
  apply TransverseNeutralPullback.pullback
  intro T a b c ha hb hc h U
  exact InterchangeNeutralFrames.horizontal_units_vertical_product P Dh Dv hi a b c ha hb hc h U

variable (f : A ⟶ B) [IsMonHom f] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)

include hi in
/-- The constructed first kernel frames respect the genuine vertical Poincare product. -/
theorem kernel_frames_transverse {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a b c : T ⟶ A ⊗ X)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X) (hb : k ≫ Kernel.Scheme.kernelInclusion f = b ≫ fst A X)
    (hc : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X) (h : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) a b c)
    (U : T.left.Opens) :
    ((sourceVertical φ P Dv).product a b c h).app U
      (((Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ).frame k a ha).hom.app U (1 : Γ(T.left, U)))
      (((Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ).frame k b hb).hom.app U (1 : Γ(T.left, U))) =
      ((Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ).frame k c hc).hom.app U (1 : Γ(T.left, U)) :=
  image_transverse φ P Dh Dv hi T a b c
    (Kernel.FramesFromNeutral.kernel_point_neutral (fst A X) f φ hφ k a ha)
    (Kernel.FramesFromNeutral.kernel_point_neutral (fst A X) f φ hφ k b hb)
    (Kernel.FramesFromNeutral.kernel_point_neutral (fst A X) f φ hφ k c hc)
    (MultiplicationFixedMap.mappedRel (snd A X) (fst A X) φ a b c h) U

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

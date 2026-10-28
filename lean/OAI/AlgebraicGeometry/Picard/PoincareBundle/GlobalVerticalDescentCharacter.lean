import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.DescentTranslation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedDescentPairing

/-! # Global Vertical Descent Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalVerticalDescentCharacter

noncomputable section

/-! The native character of a globally framed vertical family is its actual frame-ratio obstruction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (s : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ X).left)

/-- The global trivialization supplies its actual frame on any scheme-valued fiber. -/
def frame {T : Over S} (a : T ⟶ A ⊗ X) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a :=
  (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame s a.left).symm

/-- A multiplicative global frame identifies the native translation character with the inverse obstruction. -/
theorem scalar_translation {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ A)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ A ⊗ Y)
    (hz : lift x z ≫ (𝟙 A ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 A ⊗ₘ g) = q)
    (hm : (Dv.product (lift x (l ≫ Kernel.Scheme.kernelInclusion g)) (lift x z) (lift x w) (CoordinateTransverseTranslations.verticalRel _ _ _ _ h)).app ⊤
      ((GlobalVerticalDescentCharacter.frame L s (lift x (l ≫ Kernel.Scheme.kernelInclusion g))).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((GlobalVerticalDescentCharacter.frame L s (lift x z)).hom.app ⊤ (1 : Γ(T.left, ⊤))) =
        (GlobalVerticalDescentCharacter.frame L s (lift x w)).hom.app ⊤ (1 : Γ(T.left, ⊤))) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Vertical.KernelDescent.nativeDatum g L Dv Kv) s q.left (lift x z).left (lift x w).left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    ((Line.FrameUnits.frameRatio (GlobalVerticalDescentCharacter.frame L s (lift x (l ≫ Kernel.Scheme.kernelInclusion g)))
      (Kv.frame l (lift x (l ≫ Kernel.Scheme.kernelInclusion g)) (lift_snd _ _).symm))⁻¹).val := by
  let c := lift x (l ≫ Kernel.Scheme.kernelInclusion g)
  let a := lift x z
  let b := lift x w
  let hr := CoordinateTransverseTranslations.verticalRel (l ≫ Kernel.Scheme.kernelInclusion g) z w x h
  have : IsIso (Bilinear.BilinearPullback.toHom (Dv.product c a b hr)) := Dv.product_isIso c a b hr
  have he : (Vertical.KernelDescent.nativeDatum g L Dv Kv).iso q.left a.left b.left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
      asIso (Bilinear.Contraction.contractLeft (Dv.product c a b hr)
        (Kv.frame l c (lift_snd _ _).symm).hom) := by
    apply Iso.ext
    exact Vertical.DescentTranslation.native_hom_translation g L Dv Kv l z w x h q hz hw
  refine (FramedDescentPairing.scalar_eq_frameRatio (Vertical.KernelDescent.nativeDatum g L Dv Kv) s q.left a.left b.left
    (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw)).trans ?_
  change (Line.FrameUnits.frameRatio ((GlobalVerticalDescentCharacter.frame L s a) ≪≫ (Vertical.KernelDescent.nativeDatum g L Dv Kv).iso q.left a.left b.left _ _)
    (GlobalVerticalDescentCharacter.frame L s b)).val = _
  rw [he]
  apply congrArg Units.val
  exact (TransverseCharacterRatio.contraction_ratio (Dv.product c a b hr)
    (Kv.frame l c (lift_snd _ _).symm) (GlobalVerticalDescentCharacter.frame L s c) (GlobalVerticalDescentCharacter.frame L s a) (GlobalVerticalDescentCharacter.frame L s b) hm).trans
    (TransverseCharacterRatio.frameRatio_reverse (GlobalVerticalDescentCharacter.frame L s c) (Kv.frame l c (lift_snd _ _).symm))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalVerticalDescentCharacter

import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelPointPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TorsionCharacter
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.KernelTranslation

/-! # Cartier Kernel Pairing Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierKernelPairingComparison

noncomputable section

/-! Actual Cartier characters of included dual kernel points equal the inverse canonical Poincare kernel pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme)
  (φ : A.scheme ⟶ D.withPicardGroup.abelian) [IsMonHom φ]
  [IsFinite φ.left] [Flat φ.left] [Surjective φ.left]
  (Dh : FiberwiseMultiplication.Multiplication (fst D.withPicardGroup.abelian A.scheme) (snd D.withPicardGroup.abelian A.scheme)
    (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare))
  (Dv : FiberwiseMultiplication.Multiplication (snd D.withPicardGroup.abelian A.scheme) (fst D.withPicardGroup.abelian A.scheme)
    (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare))
  (hp : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh Dv)
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [IsAffine (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
    (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))))
  {B : Over (Spec (.of k))} [GrpObj B] (f : A.scheme ⟶ B) [IsMonHom f]
  [IsAffine (Kernel.Scheme.kernelObject f).left]
  (hy : (Kernel.Scheme.kernelInclusion f ≫ φ) ^ n = 1)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A.scheme A.scheme) (snd A.scheme A.scheme)
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n)) f
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh))
  (J : FiberwiseMultiplication.KernelFrames (snd A.scheme A.scheme) (fst A.scheme A.scheme)
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n)) ((𝟙 A.scheme) ^ n)
    (Poincare.TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dv))
  (hKh : Kernel.FramesTransverseTransport.Transverse f Kh (Poincare.TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dv))
  (hJ : Kernel.FramesTransverseTransport.Transverse ((𝟙 A.scheme) ^ n) J
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh))

include hp hKh hJ

/-- The constructed Cartier character evaluates to the inverse pairing on every scheme-valued kernel point. -/
theorem value {T : Over (Spec (.of k))} (a : T ⟶ Kernel.Scheme.kernelObject f)
    (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) :
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T
      ((Poincare.TorsionCharacter.character A D φ n hn C (Kernel.Scheme.kernelObject f)
        (Kernel.Scheme.kernelInclusion f ≫ φ) hy).app (.op (Over.mk a)) b)).val =
    (ConcreteKernelPairing.Concrete.value f ((𝟙 A.scheme) ^ n)
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n))
      (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh)
      (Poincare.TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dv) Kh J a
      (b ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).hom))⁻¹.val := by
  obtain ⟨s, hs⟩ := Poincare.KernelPointPairing.exists_frame_character D.withPicardGroup φ
    Dh Dv hp n f Kh J hKh hJ
  let q := lift a (1 : T ⟶ A.scheme) ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A.scheme) ^ n)
  have hb : lift a ((1 : T ⟶ A.scheme) * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n))) ≫
      (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A.scheme) ^ n) = q :=
    Intrinsic.KernelTranslation.cover ((𝟙 A.scheme) ^ n) a 1 b
  have hu := Poincare.TorsionCharacter.scalar_translation A D φ n hn C (Kernel.Scheme.kernelObject f)
    (Kernel.Scheme.kernelInclusion f ≫ φ) hy s a 1 b q rfl hb
  have hv := hs T a (b ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).hom)
    1 ((1 : T ⟶ A.scheme) * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n)))
    (Intrinsic.KernelTranslation.at_identity ((𝟙 A.scheme) ^ n) b) q rfl hb
  exact hu.symm.trans hv

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierKernelPairingComparison

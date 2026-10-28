import OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierKernelPairingComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilTorsionCharacter
import OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilUnitDetection

/-! # Weil Kernel Pairing Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilKernelPairingComparison

noncomputable section

/-! The standard Weil pairing and the canonical Poincare kernel pairing have exactly the same orthogonality condition. -/

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

/-- The actual standard Weil value on the included dual kernel point and the native torsion point. -/
def weilValue {T : Over (Spec (.of k))} (a : T ⟶ Kernel.Scheme.kernelObject f)
    (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) :
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb (Spec (.of k))).obj.obj (.op T) :=
  AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk A.scheme)) n) T
    ((AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.weilPairing A.scheme D φ n hn C).rightAdjoint.hom.app (.op T)
      ((AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk D.withPicardGroup.abelian) n).hom.hom.app (.op T)
        (ULift.up (a ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n (Kernel.Scheme.kernelInclusion f ≫ φ) hy))))
    ((AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A.scheme) n).hom.hom.app (.op T) (ULift.up b))

include hp hKh hJ

/-- The regular unit of the actual Weil value is the inverse canonical kernel pairing. -/
theorem unit_value {T : Over (Spec (.of k))} (a : T ⟶ Kernel.Scheme.kernelObject f)
    (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) :
    WeilUnitDetection.unitValue T (weilValue A D φ n hn C f hy a b) =
    (ConcreteKernelPairing.Concrete.value f ((𝟙 A.scheme) ^ n)
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n))
      (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh)
      (Poincare.TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dv) Kh J a
      (b ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).hom))⁻¹ := by
  apply Units.ext
  have hv := WeilTorsionCharacter.value A.scheme D φ n hn C (Kernel.Scheme.kernelInclusion f ≫ φ) hy a b
  have hu := congrArg (fun z => (WeilUnitDetection.unitValue T z).val) hv
  exact hu.trans (CartierKernelPairingComparison.value A D φ Dh Dv hp n hn C f hy Kh J hKh hJ a b)

/-- The standard Weil pairing detects the same orthogonality as the canonical kernel pairing on all test schemes. -/
theorem eq_one_iff {T : Over (Spec (.of k))} (a : T ⟶ Kernel.Scheme.kernelObject f)
    (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) :
    weilValue A D φ n hn C f hy a b = 1 ↔
    ConcreteKernelPairing.Concrete.value f ((𝟙 A.scheme) ^ n)
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) (φ ^ n))
      (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dh)
      (Poincare.TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.withPicardGroup.poincare) Dv) Kh J a
      (b ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).hom) = 1 := by
  constructor
  · intro h
    have hu := (WeilUnitDetection.eq_one_iff T _).mp h
    rw [unit_value A D φ Dh Dv hp n hn C f hy Kh J hKh hJ a b] at hu
    exact inv_eq_one.mp hu
  · intro h
    apply (WeilUnitDetection.eq_one_iff T _).mpr
    exact (unit_value A D φ Dh Dv hp n hn C f hy Kh J hKh hJ a b).trans (by rw [h, inv_one])

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilKernelPairingComparison

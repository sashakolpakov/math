import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionAlternation

/-! # Pairing Canonical Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PairingCanonicalValue.Construction

noncomputable section

/-! The native Poincare pairing retains the actual canonical PoincareBundle
kernel value, before any symmetry or scalar comparison is applied. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

universe u

set_option backward.isDefEq.respectTransparency false in
theorem poincareNativeTorsionPairing_canonical_value {S : Scheme.{u}} {A Z : Over S}
    [GrpObj A] [IsCommMonObj A] [GrpObj Z] [IsCommMonObj Z]
    (φ : A ⟶ Z) [IsMonHom φ] (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
    (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)
    (σn : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
    (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) σn = Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
    (hi : Picard.PoincareBundle.Biextension.Compatibility.Interchange P Dh Dv)
    (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) σn =
      Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)
    (T : Over S) (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A n) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T
      ((LineDescent.Construction.poincareNativeTorsionPairing φ P Dh Dv n σn hv hi hh).pairValue x y) =
    Picard.PoincareBundle.Canonical.KernelPairing.value (φ ^ n) P Dh Dv ((𝟙 A) ^ n)
      (Picard.PoincareBundle.TorsionPairing.Poincare.torsion_annihilation φ n) σn hv x y := by
  have h := LineDescent.Construction.poincareNativeTorsionPairing_value φ P Dh Dv n σn hv hi hh T x y
  rw [Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing, TorsionAlternation.Construction.canonicalPoincareKernelPairing_pairing_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PairingCanonicalValue.Construction

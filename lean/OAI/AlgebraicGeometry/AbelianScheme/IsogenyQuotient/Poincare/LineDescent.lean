import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSelfAnnihilator
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing

/-! # Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.LineDescent.Construction

noncomputable section

/-!
Self-annihilation of the original quotient kernel inside native torsion
gives the effective quotient line for the actual Poincare products and
their symmetry. The descended object is an HilbertConstruction line bundle and its
pullback is the original multiple Poincare line. Identifying these
products and this torsion pairing with CartierDuality's canonical polarization
construction remains a separate obligation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [GrpObj Z] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]
  (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hi : Picard.PoincareBundle.Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)

def poincareNativeTorsionPairing :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A n) (B := Torsion.Groups.Construction.nativeTorsionScheme A n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  UnitPairingTo.Construction.unitPairingToScheme (Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hi hh)
    (fun {_ _} a k l => Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing_naturality φ P Dh Dv n e hv hi hh a k l)

theorem poincareNativeTorsionPairing_value (T : Over S) (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A n) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T
      ((poincareNativeTorsionPairing φ P Dh Dv n e hv hi hh).pairValue x y) =
        Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hi hh T x y :=
  UnitPairingTo.Construction.unitPairingToScheme_unitValue _ _ T x y

variable (f : A ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (poincareNativeTorsionPairing φ P Dh Dv n e hv hi hh).relativeAnnihilator F = F)

include hlag in
set_option backward.isDefEq.respectTransparency false in
theorem poincareNativeKernel_selfAnnihilating :
    Picard.PoincareBundle.NaturalPairingOrthogonal.SelfAnnihilating (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hker)
      (Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hi hh) := by
  apply (BundleSelfAnnihilator.Construction.nativeImage_selfAnnihilating_unitPairing_iff
    (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hker)
    (Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hi hh)
    (fun {_ _} a k l => Picard.PoincareBundle.TorsionPairing.Poincare.torsionPairing_naturality φ P Dh Dv n e hv hi hh a k l)).mpr
  rw [← BundleSelfAnnihilator.Construction.nativeTorsion_kernel_eq_e45_image f n hker]
  exact hlag

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian (B ⊗ B).left]

def nativeIsotropicQuotientLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ B).left where
  sheaf := (Picard.PoincareBundle.TorsionPairing.Poincare.descendedLine φ P Dh Dv n e hv hi hh f hker
    (poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)).sheaf
  locallyTrivial := (Picard.PoincareBundle.TorsionPairing.Poincare.descendedLine φ P Dh Dv n e hv hi hh f hker
    (poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)).isLine

def nativeIsotropicQuotientLine_pullbackIso :
    (Scheme.Modules.pullback (f ⊗ₘ f).left).obj
      (nativeIsotropicQuotientLine φ P Dh Dv n e hv hi hh f hker hlag).sheaf ≅
        (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf :=
  Picard.PoincareBundle.TorsionPairing.Poincare.pullbackIso φ P Dh Dv n e hv hi hh f hker
    (poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.LineDescent.Construction

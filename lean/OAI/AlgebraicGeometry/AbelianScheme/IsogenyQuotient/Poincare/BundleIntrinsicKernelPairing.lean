import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnitPairingTo
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ConcreteKernelPairing

/-! # Bundle Intrinsic Kernel Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleIntrinsicKernelPairing.Construction

noncomputable section

/-!
The two actual PoincareBundle biextension kernel-frame systems construct a unique
native scheme pairing. Its value is exactly the ratio of the original
line-bundle frames. PoincareBundle's descent isotropy is therefore precisely
triviality of this native pairing on all kernel points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : Picard.PoincareBundle.FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : Picard.PoincareBundle.FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (ht : Picard.PoincareBundle.Biextension.Compatibility.TransverseFrames L Dh Dv f g Kh Kv)

def e45NativeKernelPairing :
    Annihilator.Construction.SchemeBicharacter (A := Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (B := Picard.PoincareBundle.Kernel.Scheme.kernelObject g)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  UnitPairingTo.Construction.unitPairingToScheme (Picard.PoincareBundle.ConcreteKernelPairing.Concrete.pairing f g L Dh Dv Kh Kv ht)
    (fun {_ _} a k l => Picard.PoincareBundle.ConcreteKernelPairing.Concrete.value_naturality f g L Dh Dv Kh Kv a k l)

theorem e45NativeKernelPairing_value (T : Over S)
    (k : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (l : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject g) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T
      ((e45NativeKernelPairing f g L Dh Dv Kh Kv ht).pairValue k l) =
        Picard.PoincareBundle.ConcreteKernelPairing.Concrete.value f g L Dh Dv Kh Kv k l :=
  UnitPairingTo.Construction.unitPairingToScheme_unitValue _ _ T k l

theorem e45NativeKernelPairing_isotropic_iff :
    Picard.PoincareBundle.Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv ↔
      ∀ (T : Over S) (k : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (l : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject g),
        (e45NativeKernelPairing f g L Dh Dv Kh Kv ht).pairValue k l = 1 := by
  rw [Picard.PoincareBundle.ConcreteKernelPairing.Concrete.isotropic_iff f g L Dh Dv Kh Kv ht]
  apply forall_congr'
  intro T
  apply forall_congr'
  intro k
  apply forall_congr'
  intro l
  exact (UnitPairingTo.Construction.unitPairingToScheme_value_eq_one_iff _ _ T k l).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleIntrinsicKernelPairing.Construction

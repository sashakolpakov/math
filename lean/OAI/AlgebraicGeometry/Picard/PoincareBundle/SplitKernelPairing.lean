import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.SplitInclusions
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PairingIsoTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.PairingValues
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PairingValues

/-! # Split Kernel Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitKernelPairing

noncomputable section

/-! The canonical pairing on the full multiple kernel, in its actual coprime product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.PairingIsoTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [GrpObj Z]
  [IsCommMonObj A] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P (φ ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hi : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)

/-- The actual canonical pairing on the entire kernel of the multiple polarization. -/
def fullPairing (T : Over S) :
    (T ⟶ Kernel.Scheme.kernelObject (φ ^ n)) →* (T ⟶ Kernel.Scheme.kernelObject (φ ^ n)) →* Γ(T.left, ⊤)ˣ :=
  Canonical.KernelPairing.pairing (φ ^ n) P Dh Dv (φ ^ n) (Kernel.Scheme.kernelInclusion_comp (φ ^ n)) e hv hi hh T

variable (d : ℕ) (hnd : n.Coprime d)
  (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)

/-- The full pairing pulled through the proved coprime kernel isomorphism. -/
def splitPairing (T : Over S) :
    (T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n) ⊗ Kernel.Scheme.kernelObject φ) →*
      (T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n) ⊗ Kernel.Scheme.kernelObject φ) →* Γ(T.left, ⊤)ˣ := by
  have : IsMonHom (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom := Kernel.Splitting.kernelProductIso_isMonHom φ n d hnd hk
  exact PairingIsoTransport.pullPairing (fullPairing φ P Dh Dv n e hv hi hh) (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom T

/-- Evaluation of the split pairing is evaluation after the actual kernel isomorphism. -/
theorem splitPairing_apply {T : Over S}
    (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n) ⊗ Kernel.Scheme.kernelObject φ) :
    splitPairing φ P Dh Dv n e hv hi hh d hnd hk T x y =
      fullPairing φ P Dh Dv n e hv hi hh T
        (x ≫ (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom) (y ≫ (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom) := by
  have : IsMonHom (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom := Kernel.Splitting.kernelProductIso_isMonHom φ n d hnd hk
  unfold splitPairing
  exact PairingIsoTransport.pullPairing_apply (fullPairing φ P Dh Dv n e hv hi hh) (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom x y

/-- Canonical frame independence gives the torsion restriction on individual test points. -/
theorem restriction_value (j : Kernel.Scheme.kernelObject ((𝟙 A) ^ n) ⟶ Kernel.Scheme.kernelObject (φ ^ n))
    (hj : j ≫ Kernel.Scheme.kernelInclusion (φ ^ n) = Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n))
    {T : Over S} (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) :
    fullPairing φ P Dh Dv n e hv hi hh T (x ≫ j) (y ≫ j) =
      TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hi hh T x y := by
  exact (Canonical.PairingValues.pairing_apply (φ ^ n) P Dh Dv (φ ^ n)
    (Kernel.Scheme.kernelInclusion_comp (φ ^ n)) e hv hi hh (x ≫ j) (y ≫ j)).trans
    ((Canonical.KernelPairing.value_restrict (φ ^ n) P Dh Dv ((𝟙 A) ^ n)
      (TorsionPairing.Poincare.torsion_annihilation φ n) e hv (φ ^ n) (Kernel.Scheme.kernelInclusion_comp (φ ^ n))
      j hj x y).symm.trans
      (Canonical.PairingValues.pairing_apply (φ ^ n) P Dh Dv ((𝟙 A) ^ n)
        (TorsionPairing.Poincare.torsion_annihilation φ n) e hv hi hh x y).symm)

/-- Restriction to the torsion factor recovers the original full-torsion pairing exactly. -/
theorem firstPairing_eq :
    CoprimeOrthogonalProduct.firstPairing (splitPairing φ P Dh Dv n e hv hi hh d hnd hk) =
      TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hi hh := by
  funext T
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  exact (Product.PairingValues.firstPairing_apply
    (splitPairing φ P Dh Dv n e hv hi hh d hnd hk) x y).trans
    ((splitPairing_apply φ P Dh Dv n e hv hi hh d hnd hk (x ≫ CoprimeOrthogonalProduct.first) (y ≫ CoprimeOrthogonalProduct.first)).trans
      ((congrArg₂ (fun a b => fullPairing φ P Dh Dv n e hv hi hh T a b)
        (Category.assoc x CoprimeOrthogonalProduct.first (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom)
        (Category.assoc y CoprimeOrthogonalProduct.first (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom)).trans
        (restriction_value φ P Dh Dv n e hv hi hh (CoprimeOrthogonalProduct.first ≫ (Kernel.Splitting.kernelProductIso φ n d hnd hk).hom)
          (by simpa only [Category.assoc] using Kernel.SplitInclusions.first_inclusion φ n d hnd hk) x y)))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitKernelPairing

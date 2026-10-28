import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.KernelPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal

/-! # Torsion Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing.Poincare

noncomputable section

/-!
# The full torsion pairing controls canonical Poincare line descent

The ambient pairing is constructed on the represented n-torsion group scheme. Its restriction
to the given quotient kernel is the canonical obstruction already used in effective descent.
Self-annihilation is imposed inside that full torsion group, on all scheme-valued points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [GrpObj Z] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]

/-- The multiple homomorphism annihilates the whole represented n-torsion subgroup scheme. -/
theorem torsion_annihilation (n : ℕ) : Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n) ≫ φ ^ n = 1 :=
  Poincare.TorsionKernelFrame.multiple_annihilates_kernel ((𝟙 A) ^ n) φ n
    (fun _T x hx => by simpa only [MonObj.comp_pow, Category.comp_id] using hx)

variable (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P (φ ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hi : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)

attribute [local instance] Kernel.Scheme.kernelGroup

/-- The normalized Poincare construction gives a bilinear pairing on the full n-torsion group scheme. -/
def torsionPairing (T : Over S) :
    (T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) →* (T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) →* Γ(T.left, ⊤)ˣ :=
  Canonical.KernelPairing.pairing (φ ^ n) P Dh Dv ((𝟙 A) ^ n) (torsion_annihilation φ n) e hv hi hh T

/-- The full torsion pairing has its genuine naturality on arbitrary, possibly nonreduced test schemes. -/
theorem torsionPairing_naturality {T T' : Over S} (a : T' ⟶ T)
    (k l : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) :
    torsionPairing φ P Dh Dv n e hv hi hh T' (a ≫ k) (a ≫ l) =
      Units.map a.left.appTop.hom (torsionPairing φ P Dh Dv n e hv hi hh T k l) :=
  Canonical.KernelPairing.value_naturality (φ ^ n) P Dh Dv ((𝟙 A) ^ n)
    (torsion_annihilation φ n) e hv a k l

variable (f : A ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f n hker)
    (torsionPairing φ P Dh Dv n e hv hi hh))

include hlag in
/-- Self-annihilation inside full torsion proves isotropy of the actual canonical quotient-kernel frames. -/
theorem kernel_isotropic :
    Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P (φ ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) f f
      (Pulled.KernelFrames.Poincare.kernelFrames (φ ^ n) P Dh f (Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker))
      (CanonicalPoincare.LineDescent.secondKernelFrames (φ ^ n) P Dh Dv f
        (Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv) := by
  apply (Canonical.KernelPairing.isotropic_iff (φ ^ n) P Dh Dv f _ e hv).mpr
  intro T k l
  exact (Canonical.KernelPairing.value_restrict (φ ^ n) P Dh Dv f _ e hv ((𝟙 A) ^ n)
    (torsion_annihilation φ n) (Kernel.ContainmentMap.torsionMap f n hker)
    (Kernel.ContainmentMap.torsionMap_inclusion f n hker) k l).trans
    (NaturalPairingOrthogonal.isotropic_of_selfAnnihilating _ _ hlag k l)

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian (B ⊗ B).left]

/-- A kernel self-annihilating inside actual n-torsion yields the effective quotient Poincare line. -/
def descendedLine : Line.Bundles.LineBundle (B ⊗ B).left :=
  CanonicalPoincare.LineDescent.descendedLine (φ ^ n) P Dh Dv hi f
    (Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
    (kernel_isotropic φ P Dh Dv n e hv hi hh f hker hlag)

/-- Pullback by the quotient product recovers the multiple Poincare line from the constructed descended line. -/
def pullbackIso : (Scheme.Modules.pullback (f ⊗ₘ f).left).obj
    (descendedLine φ P Dh Dv n e hv hi hh f hker hlag).sheaf ≅ (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf :=
  CanonicalPoincare.LineDescent.pullbackIso (φ ^ n) P Dh Dv hi f
    (Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
    (kernel_isotropic φ P Dh Dv n e hv hi hh f hker hlag)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing.Poincare

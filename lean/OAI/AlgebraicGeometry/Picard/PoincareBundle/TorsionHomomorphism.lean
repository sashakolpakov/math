import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Uniqueness

/-! # Torsion Homomorphism -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionHomomorphism.Poincare

noncomputable section

/-! The unique quotient homomorphism from self-annihilation in the full scheme-theoretic torsion group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [GrpObj Z] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]

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

variable (f : A ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f n hker)
    (TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hi hh))

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian (B ⊗ B).left]

variable [IsCommMonObj B]
  [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]
  {Bdual : Over S} [GrpObj Bdual]
  (Q : Line.Bundles.LineBundle (Bdual ⊗ B).left)
  (Qh : FiberwiseMultiplication.Multiplication (fst Bdual B) (snd Bdual B) Q)
  (Qv : FiberwiseMultiplication.Multiplication (snd Bdual B) (fst Bdual B) Q)
  (DB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy Bdual)
  (hQ : DB.homEquiv (𝟙 Bdual) = Product.Map.sectionClass Q
    (Vertical.ProductParameters.globalProduct Bdual B Q Qv)
    (Vertical.ProductParameters.globalProduct_isIso Bdual B Q Qv) (𝟙 Bdual))
  (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Z)
  (hP : DA.homEquiv (𝟙 Z) = Product.Map.sectionClass P
    (Vertical.ProductParameters.globalProduct Z A P Dv)
    (Vertical.ProductParameters.globalProduct_isIso Z A P Dv) (𝟙 Z))
  [Epi ((𝟙 B) ^ n)]

include P Dh Dv e hv hi hh hker hlag Q Qh Qv hQ hP

/-- Self-annihilation inside the full represented torsion group constructs the unique quotient homomorphism. -/
theorem existsUnique_homomorphism :
    ∃! m : B ⟶ Bdual, IsMonHom m ∧ f ≫ m ≫ DualMaps.representedDualMap DA DB f = φ ^ n :=
  CanonicalPoincare.Uniqueness.existsUnique_homomorphism (φ ^ n) P Dh Dv hi f
    (Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
    (TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker hlag)
    Q Qh Qv DB hQ DA hP n hker

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionHomomorphism.Poincare

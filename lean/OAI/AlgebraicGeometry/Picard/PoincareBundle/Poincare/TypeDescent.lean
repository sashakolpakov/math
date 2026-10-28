import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CoprimeKernelIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TypeTransport

/-! # Type Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TypeDescent

noncomputable section

/-! Maximal full-torsion isotropy preserves the complete shared polarization type under actual Poincare recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type u} [Field k] {a : ℕ}
  {A B D Z : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (φ : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Z) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B D)
  (g : D.scheme ⟶ Z.scheme) [IsMonHom g]
  (n d : ℕ) (hnd : n.Coprime d) (h : f.hom ≫ m.hom ≫ g = φ.hom ^ n)
  (v : Z.scheme ⟶ D.scheme) (hdual : g ≫ v = (𝟙 D.scheme) ^ n)
  (hk : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ φ.hom = 1 → x ^ d = 1)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (P : Line.Bundles.LineBundle (Z.scheme ⊗ A.scheme).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z.scheme A.scheme) (snd Z.scheme A.scheme) P)
  (Dv : FiberwiseMultiplication.Multiplication (snd Z.scheme A.scheme) (fst Z.scheme A.scheme) P)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj (FirstBiextensionFactor.familyLine P (φ.hom ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ.hom ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P (φ.hom ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (φ.hom ^ n) P Dh) σ =
    TransverseFrames.sourceVertical (φ.hom ^ n) P Dv)
  (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P (φ.hom ^ n))
    (TransverseFrames.sourceVertical (φ.hom ^ n) P Dv) σ = Pulled.KernelFrames.Poincare.sourceMultiplication (φ.hom ^ n) P Dh)
  (Q : Line.Bundles.LineBundle (D.scheme ⊗ B.scheme).left)
  (Qh : FiberwiseMultiplication.Multiplication (fst D.scheme B.scheme) (snd D.scheme B.scheme) Q)
  (Qv : FiberwiseMultiplication.Multiplication (snd D.scheme B.scheme) (fst D.scheme B.scheme) Q)
  (hq : Biextension.Compatibility.Interchange Q Qh Qv)
  (e : ((FirstBiextensionFactor.familyLine Q m.hom).pullback (f.hom ⊗ₘ f.hom).left).sheaf ≅ (FirstBiextensionFactor.familyLine P (φ.hom ^ n)).sheaf)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom n hf)
    (TorsionPairing.Poincare.torsionPairing φ.hom P Dh Dv n σ hv hp hh))

include hnd h hdual hk hf hp hh hq e hlag

/-- The original and descended isogenies have the same finite-flat degree and geometric kernel elementary divisors. -/
theorem hasPolarizationType (δ : Fin a → ℕ) (hφ : φ.HasPolarizationType δ) : m.HasPolarizationType δ :=
  Kernel.TypeTransport.hasPolarizationType φ m
    (CoprimeKernelIso.kernelIso φ.hom f.hom m.hom g n d hnd h v hdual hk hf
      P Dh Dv σ hv hp hh Q Qh Qv hq e hlag) δ hφ

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TypeDescent

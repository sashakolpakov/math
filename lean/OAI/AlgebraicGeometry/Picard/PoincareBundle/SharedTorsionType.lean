import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionKernelIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TypeTransport

/-! # Shared Torsion Type -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionType

noncomputable section

/-! Full-torsion self-annihilation and the actual dual pullback identity preserve the shared polarization type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A DA.abelian) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian)
  (n d : ℕ) (hn : 0 < n) (hnd : n.Coprime d)
  (hk : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ ell.hom = 1 → x ^ d = 1)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (Dh : FiberwiseMultiplication.Multiplication (fst DA.abelian.scheme A.scheme) (snd DA.abelian.scheme A.scheme) (Line.Comparison.Bundle.fromShared DA.poincare))
  (Dv : FiberwiseMultiplication.Multiplication (snd DA.abelian.scheme A.scheme) (fst DA.abelian.scheme A.scheme) (Line.Comparison.Bundle.fromShared DA.poincare))
  (Qh : FiberwiseMultiplication.Multiplication (fst DB.abelian.scheme B.scheme) (snd DB.abelian.scheme B.scheme) (Line.Comparison.Bundle.fromShared DB.poincare))
  (Qv : FiberwiseMultiplication.Multiplication (snd DB.abelian.scheme B.scheme) (fst DB.abelian.scheme B.scheme) (Line.Comparison.Bundle.fromShared DB.poincare))
  (hp : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv) (hq : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell.hom ^ n)).sheaf ≅
        (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell.hom ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell.hom ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (ell.hom ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dh) σ =
      Poincare.TransverseFrames.sourceVertical (ell.hom ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell.hom ^ n))
    (Poincare.TransverseFrames.sourceVertical (ell.hom ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dv) σ =
      Pulled.KernelFrames.Poincare.sourceMultiplication (ell.hom ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dh)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom n hf)
    (TorsionPairing.Poincare.torsionPairing ell.hom (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv n σ hv hp hh))
  (h : f.hom ≫ m.hom ≫ DualMaps.representedDualMap
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = ell.hom ^ n)

include hn hnd hk hf Dh Dv Qh Qv hp hq σ hv hh hlag h

/-- The proved kernel isomorphism preserves the entire polarization type, including inseparable kernel length. -/
theorem hasPolarizationType (δ : Fin a → ℕ) (ht : ell.HasPolarizationType δ) : m.HasPolarizationType δ := by
  have : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from ell.hom) :=
    ell.preservesGroup
  have : IsMonHom (show B.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB).abelian from m.hom) :=
    m.preservesGroup
  have : IsFinite (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from ell.hom).left :=
    ell.finite
  have : IsFinite (show B.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB).abelian from m.hom).left :=
    m.finite
  obtain ⟨e, he, _⟩ := SharedTorsionKernelIso.exists_kernelIso B
    (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)
    ell.hom f.hom m.hom n d hn hnd hk hf Dh Dv Qh Qv hp hq σ hv hh hlag h
  let e' : Kernel.Scheme.kernelObject ell.hom ≅ Kernel.Scheme.kernelObject m.hom := e
  have : IsMonHom e'.hom := he
  exact Kernel.TypeTransport.hasPolarizationType ell m e' δ ht

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionType

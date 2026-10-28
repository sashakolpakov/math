import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.FamilyRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CoprimeKernelIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedDualComplement
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveScalar
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualHomomorphism

/-! # Shared Torsion Kernel Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionKernelIso

noncomputable section

/-! Actual shared dual data, the pullback identity, and maximal torsion isotropy give the unchanged kernel without assumed family recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k)))
  {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (DA : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (DB : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B.scheme)
  (ell : A ⟶ DA.abelian) [IsMonHom ell] [IsFinite ell.left]
  (f : A ⟶ B.scheme) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (m : B.scheme ⟶ DB.abelian) [IsMonHom m] [IsFinite m.left]
  (n d : ℕ) (hn : 0 < n) (hnd : n.Coprime d)
  (hk : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ ell = 1 → x ^ d = 1)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (Dh : FiberwiseMultiplication.Multiplication (fst DA.abelian A) (snd DA.abelian A) (Line.Comparison.Bundle.fromShared DA.poincare))
  (Dv : FiberwiseMultiplication.Multiplication (snd DA.abelian A) (fst DA.abelian A) (Line.Comparison.Bundle.fromShared DA.poincare))
  (Qh : FiberwiseMultiplication.Multiplication (fst DB.abelian B.scheme) (snd DB.abelian B.scheme) (Line.Comparison.Bundle.fromShared DB.poincare))
  (Qv : FiberwiseMultiplication.Multiplication (snd DB.abelian B.scheme) (fst DB.abelian B.scheme) (Line.Comparison.Bundle.fromShared DB.poincare))
  (hp : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv) (hq : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dh) σ =
      Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell ^ n))
    (Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dv) σ =
      Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dh)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f n hf)
    (TorsionPairing.Poincare.torsionPairing ell (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv n σ hv hp hh))
  (h : f ≫ m ≫ DualMaps.representedDualMap (SharedRepresentation.representation DA) (SharedRepresentation.representation DB) f = ell ^ n)

include hn hnd hk hf Dh Dv Qh Qv hp hq σ hv hh hlag h

/-- The original kernel and quotient kernel are isomorphic by the actual restriction of the quotient map. -/
theorem exists_kernelIso : ∃ e : Kernel.Scheme.kernelObject ell ≅ Kernel.Scheme.kernelObject m,
    IsMonHom e.hom ∧ e.hom ≫ Kernel.Scheme.kernelInclusion m = Kernel.Scheme.kernelInclusion ell ≫ f := by
  have : LocallyOfFiniteType (B.scheme ⊗ B.scheme).hom := Product.Noetherian.product_finiteType B.scheme B.scheme
  have : IsLocallyNoetherian (B.scheme ⊗ B.scheme).left := Product.Noetherian.product_noetherian B.scheme B.scheme
  have : IsLocallyNoetherian ((B.scheme ⊗ B.scheme) ⊗ B.scheme).left :=
    Product.Noetherian.product_noetherian (B.scheme ⊗ B.scheme) B.scheme
  have : IsLocallyNoetherian (B.scheme ⊗ (B.scheme ⊗ B.scheme)).left :=
    Product.Noetherian.product_noetherian B.scheme (B.scheme ⊗ B.scheme)
  have : IsLocallyNoetherian B.scheme.left := LocallyOfFiniteType.isLocallyNoetherian B.scheme.hom
  have : EffectiveEpi ((𝟙 B.scheme) ^ n) := PositiveScalar.quotient_scalar_effective DA ell f n hn
  let hP := SharedRepresentation.universalClass DA
    (Vertical.ProductParameters.globalProduct DA.abelian A (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
    (Vertical.ProductParameters.globalProduct_isIso DA.abelian A (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
  let hQ := SharedRepresentation.universalClass DB
    (Vertical.ProductParameters.globalProduct DB.abelian B.scheme (Line.Comparison.Bundle.fromShared DB.poincare) Qv)
    (Vertical.ProductParameters.globalProduct_isIso DB.abelian B.scheme (Line.Comparison.Bundle.fromShared DB.poincare) Qv)
  have : IsMonHom (DualMaps.representedDualMap (SharedRepresentation.representation DA) (SharedRepresentation.representation DB) f) :=
    DualHomomorphism.representedDualMap_isMonHom (SharedRepresentation.representation DA) (SharedRepresentation.representation DB)
      (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv hP hQ f
  obtain ⟨v, hvdual⟩ := SharedDualComplement.exists_dual_complement DA DB Qh Qv f n hf
  obtain ⟨er⟩ := CanonicalPoincare.FamilyRecovery.Family.exists_recovery_of_pullback B (ell ^ n)
    (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv hp f (Poincare.TorsionKernelFrame.multiple_annihilates_kernel f ell n hf)
    σ hv hh (TorsionPairing.Poincare.kernel_isotropic ell (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv n σ hv hp hh f hf hlag)
    DB Qv Qh (SharedRepresentation.representation DA) hP n hf m h
  let e := Poincare.CoprimeKernelIso.kernelIso ell f m
    (DualMaps.representedDualMap (SharedRepresentation.representation DA) (SharedRepresentation.representation DB) f) n d hnd h v hvdual hk hf
    (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv σ hv hp hh (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv hq er hlag
  refine ⟨e, inferInstance, ?_⟩
  exact CoprimeKernelEmbedding.map_inclusion ell f m
    (DualMaps.representedDualMap (SharedRepresentation.representation DA) (SharedRepresentation.representation DB) f) n d hnd h v hvdual hk

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionKernelIso

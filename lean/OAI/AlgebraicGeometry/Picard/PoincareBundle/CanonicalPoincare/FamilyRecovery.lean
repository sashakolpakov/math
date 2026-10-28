import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.FamilyIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Uniqueness

/-! # Family Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.FamilyRecovery.Family

noncomputable section

/-! The constructed quotient homomorphism recovers the original actual Poincare family, without an assumed recovery isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {A Z : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hi : Biextension.Compatibility.Interchange P Dh Dv) (f : A ⟶ B.scheme) [IsMonHom f] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) σ = Poincare.TransverseFrames.sourceVertical φ P Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) σ =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
  (he : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv)
    f f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) (LineDescent.secondKernelFrames φ P Dh Dv f hφ σ hv))
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B.scheme ⊗ B.scheme).left]
  [IsLocallyNoetherian (B.scheme ⊗ (B.scheme ⊗ B.scheme)).left] [IsLocallyNoetherian B.scheme.left]
  (DB : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B.scheme)
  (Qv : FiberwiseMultiplication.Multiplication (snd DB.abelian B.scheme) (fst DB.abelian B.scheme) (Line.Comparison.Bundle.fromShared DB.poincare))

include Qv

/-- The canonical represented quotient map has an actual Poincare recovery isomorphism. -/
theorem exists_recovery : Nonempty
    (((FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DB.poincare)
      (Map.representedMap φ P Dh Dv hi f hφ σ hv hh he (SharedRepresentation.representation DB))).pullback
        (f ⊗ₘ f).left).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf) := by
  obtain ⟨d⟩ := FamilyIso.Family.exists_familyIso B φ P Dh Dv hi f hφ σ hv hh he DB Qv
  exact ⟨(Scheme.Modules.pullback (f ⊗ₘ f).left).mapIso d.symm ≪≫ LineDescent.pullbackIso φ P Dh Dv hi f hφ σ hv hh he⟩

variable [IsLocallyNoetherian ((B.scheme ⊗ B.scheme) ⊗ B.scheme).left]
  (Qh : FiberwiseMultiplication.Multiplication (fst DB.abelian B.scheme) (snd DB.abelian B.scheme) (Line.Comparison.Bundle.fromShared DB.poincare))
  (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Z)
  (hP : DA.homEquiv (𝟙 Z) = Product.Map.sectionClass P
    (Vertical.ProductParameters.globalProduct Z A P Dv)
    (Vertical.ProductParameters.globalProduct_isIso Z A P Dv) (𝟙 Z))
  (n : ℕ) (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  [Epi ((𝟙 B.scheme) ^ n)]

include Qh hP hker Dh hi hφ σ hv hh he

/-- Every homomorphism satisfying the proved unique pullback identity inherits the actual canonical family recovery. -/
theorem exists_recovery_of_pullback (m : B.scheme ⟶ DB.abelian) [IsMonHom m]
    (hm : f ≫ m ≫ DualMaps.representedDualMap DA (SharedRepresentation.representation DB) f = φ) :
    Nonempty (((FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DB.poincare) m).pullback (f ⊗ₘ f).left).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf) := by
  have hm' := Uniqueness.representedMap_unique φ P Dh Dv hi f hφ σ hv hh he
    (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv (SharedRepresentation.representation DB)
    (SharedRepresentation.universalClass DB (Vertical.ProductParameters.globalProduct DB.abelian B.scheme (Line.Comparison.Bundle.fromShared DB.poincare) Qv)
      (Vertical.ProductParameters.globalProduct_isIso DB.abelian B.scheme (Line.Comparison.Bundle.fromShared DB.poincare) Qv))
    DA hP n hker m hm
  rw [hm']
  exact exists_recovery B φ P Dh Dv hi f hφ σ hv hh he DB Qv

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.FamilyRecovery.Family

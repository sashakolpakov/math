import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Homomorphism
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.PoincarePullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackInjective

/-! # Uniqueness -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Uniqueness

noncomputable section

/-! Uniqueness of the canonical quotient homomorphism from its dual pullback identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hi : Biextension.Compatibility.Interchange P Dh Dv) (f : A ⟶ B) [IsMonHom f] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) symmetry = Poincare.TransverseFrames.sourceVertical φ P Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) symmetry =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
  (he : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv)
    f f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) (LineDescent.secondKernelFrames φ P Dh Dv f hφ symmetry hv))
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

variable [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]
  {Bdual : Over S} [GrpObj Bdual]
  (Q : Line.Bundles.LineBundle (Bdual ⊗ B).left)
  (Qh : FiberwiseMultiplication.Multiplication (fst Bdual B) (snd Bdual B) Q)
  (Qv : FiberwiseMultiplication.Multiplication (snd Bdual B) (fst Bdual B) Q)
  (DB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy Bdual)
  (hQ : DB.homEquiv (𝟙 Bdual) = Product.Map.sectionClass Q
    (Vertical.ProductParameters.globalProduct Bdual B Q Qv)
    (Vertical.ProductParameters.globalProduct_isIso Bdual B Q Qv) (𝟙 Bdual))

variable [IsCommMonObj B]
  (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Z)
  (hP : DA.homEquiv (𝟙 Z) = Product.Map.sectionClass P
    (Vertical.ProductParameters.globalProduct Z A P Dv)
    (Vertical.ProductParameters.globalProduct_isIso Z A P Dv) (𝟙 Z))
  (n : ℕ) (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  [Epi ((𝟙 B) ^ n)]

include Q Qh Qv hQ hP n hker Dh hi hφ symmetry hv hh he

/-- The canonical descended homomorphism is uniquely determined by its actual dual pullback. -/
theorem representedMap_unique (m : B ⟶ Bdual) [IsMonHom m]
    (hm : f ≫ m ≫ DualMaps.representedDualMap DA DB f = φ) :
    m = Map.representedMap φ P Dh Dv hi f hφ symmetry hv hh he DB := by
  have : IsMonHom (Map.representedMap φ P Dh Dv hi f hφ symmetry hv hh he DB) :=
    Homomorphism.representedMap_isMonHom φ P Dh Dv hi f hφ symmetry hv hh he Q Qh Qv DB hQ
  exact PullbackInjective.affine_pullback_injective DA DB Q Qh Qv hQ f n hker m _
    (hm.trans (PoincarePullback.representedMap_pullback φ P Dh Dv hi f hφ symmetry hv hh he DA DB hP).symm)

/-- The line descent constructs the unique homomorphism satisfying the prescribed dual pullback identity. -/
theorem existsUnique_homomorphism :
    ∃! m : B ⟶ Bdual, IsMonHom m ∧ f ≫ m ≫ DualMaps.representedDualMap DA DB f = φ := by
  refine ⟨Map.representedMap φ P Dh Dv hi f hφ symmetry hv hh he DB, ⟨?_, ?_⟩, ?_⟩
  · exact Homomorphism.representedMap_isMonHom φ P Dh Dv hi f hφ symmetry hv hh he Q Qh Qv DB hQ
  · exact PoincarePullback.representedMap_pullback φ P Dh Dv hi f hφ symmetry hv hh he DA DB hP
  · intro m hm
    have : IsMonHom m := hm.1
    exact representedMap_unique φ P Dh Dv hi f hφ symmetry hv hh he Q Qh Qv DB hQ DA hP n hker m hm.2

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Uniqueness

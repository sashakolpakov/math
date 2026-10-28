import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ParameterCharacterRecovery
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardPullback

/-! # Geometric Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.GeometricKernel.Construction

noncomputable section

/-! Every geometric point of the actual relative Picard pullback
kernel comes from the original Cartier character subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : X ⟶ A.scheme) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left] (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

set_option backward.isDefEq.respectTransparency false in
theorem canonicalPicardPullback_geometric_kernel_lift
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)
    (z : Over.mk s ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
    (hz : Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f (Over.mk s) z = 1) :
    ∃ x : Over.mk s ⟶ C.dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C = z := by
  let T := Over.mk s
  let y := (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv z
  let L := D.poincare.pullback (z ▷ A.scheme).left
  have hy : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A.scheme).hom.app (op T) y :=
    Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) z
  have hrel := UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullback_kernel_relative f T y
    ((UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply f T y).symm.trans hz)
  rw [← hy, Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply] at hrel
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 T) ⊗ₘ f).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ X).left := by
    rw [id_tensorHom]
    exact (Relative.CartierInjection.Construction.toSheafify_geometric_bijective s (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf X)).injective hrel
  obtain ⟨χ, hχ⟩ := Geometric.ParameterCharacterRecovery.Construction.exists_kernelCharacter_of_geometric_productLine f s L hc y hy
  let x := (C.sectionEquiv T).symm χ
  refine ⟨x, ?_⟩
  apply (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv.injective
  change (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv (x ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) C) = y
  rw [CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply]
  change (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv
    ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv.symm
      (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T x))) = y
  rw [Equiv.apply_symm_apply, show C.sectionEquiv T x = χ from (C.sectionEquiv T).apply_symm_apply χ]
  exact hχ

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.GeometricKernel.Construction

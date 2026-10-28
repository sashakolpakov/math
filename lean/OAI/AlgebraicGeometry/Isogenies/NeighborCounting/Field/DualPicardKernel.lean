import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteAbelianHomIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardExactness

/-! # Dual Picard Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.DualPicardKernel

noncomputable section

/-! The actual Picard pullback kernel is the finite Cartier character
kernel over the original field. This constructs the dual isogeny without
replacing the field by an algebraic closure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardExactness.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteAbelianHomIsogeny

variable {k : Type} [Field k] {g : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

theorem fieldDualPicardPullback_isMonHom : IsMonHom (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom) := by
  have h := Picard.Homomorphisms.DualHomomorphism.Construction.dualPicardPullback_isMonHom f.hom DA DB
  rw [ReducedPicardSheafRepresentation.givenDualPicardGroup_eq DA,
    ReducedPicardSheafRepresentation.givenDualPicardGroup_eq DB] at h
  exact h

theorem fieldDualPicardPullback_kernel (T : Over (Spec (.of k))) (x : T ⟶ DB.abelian.scheme) :
    x ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom = 1 ↔
      ∃! y : T ⟶ (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X, y ≫ AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f = x := by
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType (by rw [f.hom.w]; infer_instance) inferInstance
  have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f).left := AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion_closed DB f
  have : Mono (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f) := Over.mono_of_mono_left _
  constructor
  · intro hx
    have hc : (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A.scheme B.scheme f.hom).hom.app (.op T)
        (DB.representable.homEquiv x) = Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A.scheme T :=
      (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_representation DA DB f.hom x).symm.trans
        ((congrArg DA.representable.homEquiv hx).trans (DA.origin T))
    obtain ⟨χ, hχ, _⟩ := AbelianScheme.FrobeniusKernel.PicardExactness.Construction.picardPullback_kernel_character_unique f.hom T (DB.representable.homEquiv x) hc
    let y := ((AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T).symm χ
    have hy : (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T y = χ :=
      ((AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T).apply_symm_apply χ
    have he : y ≫ AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f = x := DB.representable.homEquiv.injective
      ((AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters.cartierToPicard_representation f.hom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)
        (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f) T y).trans
          ((congrArg (AbelianScheme.CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f.hom T) hy).trans hχ))
    exact ⟨y, he, fun z hz => (cancel_mono (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f)).mp (hz.trans he.symm)⟩
  · rintro ⟨y, hy, _⟩
    rw [← hy]
    apply DA.representable.homEquiv.injective
    exact (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_representation DA DB f.hom (y ≫ AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f)).trans
      ((AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion_pullback DB f T y).trans (DA.origin T).symm)

theorem fieldDualPicardPullback_finite : IsFinite (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom).left := by
  have : IsMonHom (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom) := fieldDualPicardPullback_isMonHom DA DB f
  have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f).left := AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion_closed DB f
  have : Mono (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f) := Over.mono_of_mono_left _
  have : IsFinite (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X.hom := (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).finite
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom)).hom :=
    PrescribedKernelIso.prescribedKernel_finite (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom)
      (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion DB f)
      (fieldDualPicardPullback_kernel DA DB f)
  exact Picard.Homomorphisms.FiniteGroupMaps.Construction.groupHom_finite_of_finite_kernel (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom)

def fieldDualPicardIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny DB.abelian DA.abelian := by
  have : IsMonHom (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom) := fieldDualPicardPullback_isMonHom DA DB f
  have : IsFinite (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom).left := fieldDualPicardPullback_finite DA DB f
  exact FiniteAbelianHomIsogeny.finiteAbelianHomIsogenyOverBase DB.abelian DA.abelian (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f.hom)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.DualPicardKernel

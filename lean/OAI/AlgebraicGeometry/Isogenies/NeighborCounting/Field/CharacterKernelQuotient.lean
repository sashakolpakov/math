import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.KernelQuotient
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPicardSheafRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterQuotient

/-! # Character Kernel Quotient -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

noncomputable section

/-! The character kernel embeds in the original dual over the evaluation
field. Its actual abelian quotient is constructed without assuming that
the field is algebraically closed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.KernelQuotient

variable {k : Type u} [Field k] {g h : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)

theorem fieldCharacterInclusion_isMonHom : IsMonHom (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f) := by
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (by rw [f.hom.w]; infer_instance) inferInstance
  have hh := AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_isMonHom f.hom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)
    (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f)
  rw [AbelianScheme.IsogenyQuotient.ReducedGroupRigidity.Construction.dualPicardGroup_eq_given_over_reduced_base] at hh
  exact hh

def fieldCharacterQuotient :
    AbelianScheme.FrobeniusKernel.GeometricQuotient.Construction.GeometricKernelQuotient D.abelian (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f) := by
  have : IsMonHom (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f) := fieldCharacterInclusion_isMonHom D f
  exact KernelQuotient.fieldKernelQuotient D.abelian _ _ (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion_closed D f)
    ⟨(AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).finite, (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).flat,
      (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).finitelyPresented⟩

def fieldCharacterAbelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)) :=
  KernelQuotient.fieldAbelian (fieldCharacterQuotient D f)

def fieldCharacterIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny D.abelian (fieldCharacterAbelian D f) :=
  KernelQuotient.fieldIsogeny (fieldCharacterQuotient D f)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

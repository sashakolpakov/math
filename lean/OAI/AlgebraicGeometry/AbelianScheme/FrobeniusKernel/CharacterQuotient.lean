import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicard
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ConstructedQuotientData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DualDataEquality
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Character Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction

noncomputable section

/-! The kernel-character subgroup of an isogeny embeds into the known
source dual and has an actual abelian quotient. Applied to a complementary
isogeny, this constructs the scheme used for the quotient dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)

def isogenyKernelCharacters :
    CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom)) := by
  have hp : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (by rw [f.hom.w]; infer_instance) inferInstance
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f.hom ⟨f.finite, f.flat, hp⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom).hom := hK.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom).hom := hK.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom).hom := hK.2.2
  have : IsCommMonObj (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom) := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative f.hom
  exact CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom))

def isogenyCharacterInclusion : (isogenyKernelCharacters f).dual.X ⟶ DA.abelian.scheme := by
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (by rw [f.hom.w]; infer_instance) inferInstance
  exact CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f.hom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) (isogenyKernelCharacters f)

theorem isogenyCharacterInclusion_isMonHom : IsMonHom (isogenyCharacterInclusion DA f) := by
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (by rw [f.hom.w]; infer_instance) inferInstance
  have hh := CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_isMonHom f.hom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) (isogenyKernelCharacters f)
  rw [Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)] at hh
  exact hh

omit [IsAlgClosed k] in
theorem isogenyCharacterInclusion_closed : IsClosedImmersion (isogenyCharacterInclusion DA f).left := by
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (by rw [f.hom.w]; infer_instance) inferInstance
  have hm : Mono (isogenyCharacterInclusion DA f) :=
    CartierDuality.PicardMonomorphism.Construction.KernelCharacters.cartierToPicard_mono f.hom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) (isogenyKernelCharacters f)
  have : IsFinite (isogenyKernelCharacters f).dual.X.hom := (isogenyKernelCharacters f).finite
  have : IsFinite ((isogenyCharacterInclusion DA f).left ≫ DA.abelian.scheme.hom) := by
    rw [(isogenyCharacterInclusion DA f).w]
    infer_instance
  have : IsFinite (isogenyCharacterInclusion DA f).left :=
    IsFinite.of_comp (isogenyCharacterInclusion DA f).left DA.abelian.scheme.hom
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

def isogenyCharacterQuotient :
    GeometricQuotient.Construction.GeometricKernelQuotient DA.abelian (isogenyKernelCharacters f).dual (isogenyCharacterInclusion DA f) := by
  have : IsMonHom (isogenyCharacterInclusion DA f) := isogenyCharacterInclusion_isMonHom DA f
  exact GeometricQuotient.Construction.geometricKernelQuotient DA.abelian _ _ (isogenyCharacterInclusion_closed DA f)
    ⟨(isogenyKernelCharacters f).finite, (isogenyKernelCharacters f).flat,
      (isogenyKernelCharacters f).finitelyPresented⟩

omit [IsAlgClosed k] in
theorem isogenyCharacterInclusion_pullback (T : Over (Spec (.of k)))
    (x : T ⟶ (isogenyKernelCharacters f).dual.X) :
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B.scheme A.scheme f.hom).hom.app (.op T)
      (DA.representable.homEquiv (x ≫ isogenyCharacterInclusion DA f)) =
        Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass B.scheme T := by
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (by rw [f.hom.w]; infer_instance) inferInstance
  have hx := CartierDuality.PicardMonomorphism.Construction.KernelCharacters.cartierToPicard_representation f.hom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)
    (isogenyKernelCharacters f) T x
  exact (congrArg ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B.scheme A.scheme f.hom).hom.app (.op T)) hx).trans
    (CharacterPicard.Construction.parameterCharacterPicardHom_pullback f.hom T ((isogenyKernelCharacters f).sectionEquiv T x))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction

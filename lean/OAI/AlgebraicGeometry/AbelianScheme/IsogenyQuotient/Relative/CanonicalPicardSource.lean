import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.SourceKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageSourceGroup
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Finite
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualData

/-! # Canonical Picard Source -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CanonicalPicardSource.Construction

noncomputable section

/-! The actual Picard source map is an isogeny to the original
representative with its canonical tensor-product group law, over the
entire characteristic-zero base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A B Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (i : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj) [Mono i]
  (F : ∀ T : Over S, (T ⟶ Q.scheme) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj.obj (op T))
  (hF : ∀ (T : Over S) (x : T ⟶ Q.scheme), F T x = i.app (op T) (ULift.up x))
  {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
  (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)

set_option backward.isDefEq.respectTransparency false in
def relativeCanonicalPicardSourceIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny Q (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian := by
  let D' := (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup
  let m := PicardImage.SourceMap.Construction.picardImageSourceMap D' f.hom i
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (show LocallyOfFinitePresentation (f.hom.left ≫ B.scheme.hom) from
        f.hom.w.symm ▸ inferInstance) inferInstance
  have : IsMonHom m := Canonical.PicardImageSourceGroup.Construction.canonicalPicardImageSourceMap_isMonHom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) f.hom i F hF
  have : IsFinite m.left := RelativePicard.SourceKernel.Construction.relativePicardImageSourceMap_finite D' f.hom
    (Finite.FlatKernelCartierRepresentation.Construction.finiteFlatKernelCartierRepresentation f.hom) i p n hn hk
  exact Finite.Construction.relativeFiniteAbelianHomIsogeny Q (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian m

theorem relativeCanonicalPicardSourceIsogeny_hom :
    (relativeCanonicalPicardSourceIsogeny D f i F hF p n hn hk).hom =
      PicardImage.SourceMap.Construction.picardImageSourceMap (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) f.hom i := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CanonicalPicardSource.Construction

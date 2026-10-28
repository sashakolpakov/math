import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageFromGeometric
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CanonicalPicardSource
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GeometricSections

/-! # Image From Duals -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageFromDuals.Construction

noncomputable section

/-! The original source dual and the already constructed geometric
quotient duals identify a same-dimension relative Picard image with the
entire homogeneous Picard sheaf over an arbitrary characteristic-zero base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A B Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (i : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj) [Mono i]
  (F : ∀ T : Over S, (T ⟶ Q.scheme) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj.obj (op T))
  (hF : ∀ (T : Over S) (x : T ⟶ Q.scheme), F T x = i.app (op T) (ULift.up x))
  (hgeo : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    Nonempty (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData (B.pullback s)))

include D f F hF hgeo in
set_option backward.isDefEq.respectTransparency false in
theorem relativePicardImage_isIso_of_geometric_duals
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1) : IsIso i := by
  let D' := (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup
  let m := Relative.CanonicalPicardSource.Construction.relativeCanonicalPicardSourceIsogeny D f i F hF p n hn hk
  have hm : m.hom = PicardImage.SourceMap.Construction.picardImageSourceMap D' f.hom i :=
    Relative.CanonicalPicardSource.Construction.relativeCanonicalPicardSourceIsogeny_hom D f i F hF p n hn hk
  have : IsFinite (PicardImage.SourceMap.Construction.picardImageSourceMap D' f.hom i).left := hm ▸ m.finite
  have : Flat (PicardImage.SourceMap.Construction.picardImageSourceMap D' f.hom i).left := hm ▸ m.flat
  have : Surjective (PicardImage.SourceMap.Construction.picardImageSourceMap D' f.hom i).left := hm ▸ m.surjective
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (show LocallyOfFinitePresentation (f.hom.left ≫ B.scheme.hom) from
        f.hom.w.symm ▸ inferInstance) inferInstance
  have : LocallyOfFinitePresentation (PicardImage.SourceMap.Construction.picardImageSourceMap D' f.hom i).left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
      (show LocallyOfFinitePresentation ((PicardImage.SourceMap.Construction.picardImageSourceMap D' f.hom i).left ≫ D'.abelian.hom) from
        (PicardImage.SourceMap.Construction.picardImageSourceMap D' f.hom i).w.symm ▸ inferInstanceAs (LocallyOfFinitePresentation Q.scheme.hom))
      inferInstance
  apply ImageFromGeometric.Construction.relativePicardImage_isIso_of_geometric_sections D' f.hom
    (Finite.FlatKernelCartierRepresentation.Construction.finiteFlatKernelCartierRepresentation f.hom) i F hF ?_ p n hn hk
  intro K _ _ s
  obtain ⟨DB⟩ := hgeo K s
  have : IsIso (PicardImage.BaseChange.Construction.picardImageBaseChangeMap i s) := Geometric.PicardImageIso.Construction.geometricBaseChangePicardImage_isIso B Q i s DB
  exact PicardImage.GeometricSections.Construction.picardImage_geometric_sections_surjective i s

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageFromDuals.Construction

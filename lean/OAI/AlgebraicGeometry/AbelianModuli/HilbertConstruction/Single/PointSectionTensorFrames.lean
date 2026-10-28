import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionSpanning
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleRationalFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointBaseSectionFrames

/-! # Point Section Tensor Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointSectionTensorFrames

noncomputable section

/-! A surjective field pullback with trivial line bundle detects a global frame when the actual section tensor comparison is surjective. In particular, this applies to the residue fiber over a one-point, possibly nonreduced, base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem lineBundle_trivial_of_surjective_field_section_tensor
    {K : Type u} [Field K] {S X P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Spec (.of K)} {f : X ⟶ S} {g : Spec (.of K) ⟶ S}
    (H : IsPullback a b f g) [UniversallyClosed b] [IsReduced P] [ConnectedSpace P]
    (ha : Function.Surjective a) (L : Line.Bundles.LineBundle X)
    (e : (L.pullback a).sheaf ≅ Line.Bundles.structureModule P)
    (y : Spec (.of K) ⟶ P) (hy : y ≫ b = 𝟙 _)
    (hsurj : Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (op ⊤))) :
    Nonempty (L.sheaf ≅ Line.Bundles.structureModule X) := by
  let k : Spec (.of K) := IsLocalRing.closedPoint K
  let t : Line.Bundles.structureModule P ⟶ (L.pullback a).sheaf := e.inv
  have ht : Ample.LineBundles.sectionNonvanishing t = ⊤ := Ample.LineBundles.sectionNonvanishing_of_isIso t
  have hyt : y k ∈ Ample.LineBundles.sectionNonvanishing t := ht.symm ▸ (show y k ∈ (⊤ : P.Opens) from trivial)
  obtain ⟨s, hs⟩ := Geometric.SectionSpanning.exists_section_nonvanishing_of_tensor_surjective H L hsurj (y k) t hyt
  let sa : Line.Bundles.structureModule P ⟶ (L.pullback a).sheaf := Ample.LineBundles.pullbackSection a s
  have hsa : y k ∈ Ample.LineBundles.sectionNonvanishing sa :=
    (congrArg (fun V : P.Opens => y k ∈ V)
      (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange a L s)).mpr hs
  have hframe : IsIso (Ample.LineBundles.pullbackSection y sa) := by
    apply (Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
    rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange y (L.pullback a) sa]
    apply top_unique
    intro z _
    change y z ∈ Ample.LineBundles.sectionNonvanishing sa
    exact (congrArg (fun q : Spec (.of K) => y q ∈ Ample.LineBundles.sectionNonvanishing sa)
      (Subsingleton.elim z k)).mpr hsa
  have hsaIso : IsIso sa := LineBundleRationalFrames.trivialLineBundle_section_isIso_of_rationalFiber b y hy (L.pullback a) e sa
  have : IsIso (Ample.LineBundles.pullbackSection a s) := hsaIso
  have : IsIso s := PointBaseSectionFrames.lineBundle_section_isIso_of_surjective_pullback a ha L s
  exact ⟨(asIso s).symm⟩

theorem lineBundle_trivial_of_single_fiber_section_tensor
    {S X : Scheme.{u}} [Subsingleton S] (f : X ⟶ S) (x : S)
    [UniversallyClosed (f.fiberToSpecResidueField x)] [IsReduced (f.fiber x)]
    [ConnectedSpace (f.fiber x)] (L : Line.Bundles.LineBundle X)
    (e : (L.pullback (f.fiberι x)).sheaf ≅ Line.Bundles.structureModule (f.fiber x))
    (y : Spec (S.residueField x) ⟶ f.fiber x)
    (hy : y ≫ f.fiberToSpecResidueField x = 𝟙 _)
    (hsurj : Function.Surjective
      ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison (IsPullback.of_hasPullback f (S.fromSpecResidueField x))
        L.sheaf).app (op ⊤))) :
    Nonempty (L.sheaf ≅ Line.Bundles.structureModule X) := by
  exact lineBundle_trivial_of_surjective_field_section_tensor
    (K := S.residueField x) (a := f.fiberι x) (b := f.fiberToSpecResidueField x)
    (f := f) (g := S.fromSpecResidueField x)
    (IsPullback.of_hasPullback f (S.fromSpecResidueField x))
    (PointBaseSectionFrames.fiberInclusion_surjective_of_subsingleton_base f x) L e y hy hsurj

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointSectionTensorFrames

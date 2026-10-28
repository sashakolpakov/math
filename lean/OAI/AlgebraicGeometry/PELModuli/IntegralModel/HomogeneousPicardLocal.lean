import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Homogeneous Picard Local -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardLocal

noncomputable section

/-! Homogeneity of a concrete line-bundle class is local for the fppf
topology on its test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

theorem homogeneousPicard_of_cover {S : Scheme.{u}} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (T : Over S)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T))
    (R : Sieve T) (hR : R ∈ (Scheme.fppfTopology.over S) T)
    (hlocal : ∀ {U : Over S} (f : U ⟶ T), R f →
      A.IsHomogeneousPicardClass U ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q)) :
    A.IsHomogeneousPicardClass T q := by
  intro U f a
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).property
  apply (hF (R.pullback f) ((Scheme.fppfTopology.over S).pullback_stable f hR)).isSeparatedFor.ext
  intro W k hk
  let qU := (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q
  have hh := hlocal (k ≫ f) hk W (𝟙 W) (k ≫ a)
  simp only [op_comp, op_id, Functor.map_comp_apply, Functor.map_id_apply] at hh
  exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme k
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left qU)).trans
      ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op W))
        (A.translationClass_naturality k a qU)).trans
          (hh.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme k qU).symm))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardLocal

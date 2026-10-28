import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldGraphEmbeddings
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientFrames
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreSectionPowers

/-! # Field Graph Twists -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldGraphTwists

noncomputable section

/-! Actual native twists on the projective field embedding of a relative graph. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace PolarizationEmbedding
variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme))
    {K : Type} [Field K] (a : Spec (.of K) ⟶ S)
    (v : (A.pullback a).scheme ⟶ (A.pullback a).scheme)

variable (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) {n : ℕ}
  (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left ⟶ P.sheaf))
  (hs : ∀ x : A.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
  (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.scheme.hom s hs).left)
  (hSegre : HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation
    (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.scheme P s hs he) (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.scheme P s hs he) B)

include hSegre in
theorem relativeFieldGraphEmbedding_twists (j : Fin (B.dimension + 1)) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback (FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A B a v)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j m) ≅
        (((Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34ProductLine A.scheme P).tensorPower m).pullback (GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct A (Over.mk a) v)).sheaf) := by
  let f := FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A B a v
  let q := AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a) B.dimension
  let w := GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct A (Over.mk a) v
  let H := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := Γ(S, ⊤)) j m
  obtain ⟨hbase⟩ := Projective.CoefficientFrames.PolarizationEmbedding.coefficientHyperplane_powers_iso (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a).hom j m
  obtain ⟨hsegre⟩ := SegreSectionPowers.PolarizationEmbedding.e34SegreSection_powers A.scheme P s hs he B hSegre j m
  have hfq : f ≫ q = w ≫ B.coefficientEmbedding := FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_coefficient A B a v
  exact ⟨(Scheme.Modules.pullback f).mapIso hbase.symm ≪≫
    (Scheme.Modules.pullbackComp f q).app H ≪≫
    (Scheme.Modules.pullbackCongr hfq).app H ≪≫
    (Scheme.Modules.pullbackComp w B.coefficientEmbedding).symm.app H ≪≫
    (Scheme.Modules.pullback w).mapIso hsegre⟩

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldGraphTwists

import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldSourceEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientFrames
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreSectionPowers

/-! # Field Source Twists -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldSourceTwists

noncomputable section

/-! Native twists on a geometric source fiber are the actual pullbacks
of the powers of the line defining the section embedding. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding
variable {S : Scheme.{0}} (X : Over S) (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) {n : ℕ}
    (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ P.sheaf))
    (hs : ∀ x : X.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).left)
    {K : Type} [Field K] (a : Spec (.of K) ⟶ S)

theorem relativeFieldSourceEmbedding_twists (j : Fin (n + 1)) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback
      (FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation X P s hs he) a)).obj
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j m) ≅
      ((P.tensorPower m).pullback (pullback.fst X.hom a)).sheaf) := by
  let B := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation X P s hs he
  let f := FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding B a
  let q := AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a) n
  let w := pullback.fst X.hom a
  let H := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := Γ(S, ⊤)) j m
  obtain ⟨hbase⟩ := Projective.CoefficientFrames.PolarizationEmbedding.coefficientHyperplane_powers_iso (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a).hom j m
  have hp : Nonempty ((Scheme.Modules.pullback B.coefficientEmbedding).obj H ≅
      (P.tensorPower m).sheaf) := by
    rw [show B.coefficientEmbedding = AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism X.hom s hs from
      SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation_coefficient X P s hs he]
    exact IntrinsicProjectivePowers.PolarizationEmbedding.nativeHyperplane_section_pullback P X.hom s hs j m
  obtain ⟨hsource⟩ := hp
  have hfq : f ≫ q = w ≫ B.coefficientEmbedding := FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_coefficient B a
  exact ⟨(Scheme.Modules.pullback f).mapIso hbase.symm ≪≫
    (Scheme.Modules.pullbackComp f q).app H ≪≫
    (Scheme.Modules.pullbackCongr hfq).app H ≪≫
    (Scheme.Modules.pullbackComp w B.coefficientEmbedding).symm.app H ≪≫
    (Scheme.Modules.pullback w).mapIso hsource⟩

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldSourceTwists

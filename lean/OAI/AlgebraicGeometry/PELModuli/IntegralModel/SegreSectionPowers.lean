import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreHyperplaneComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackPowers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.GraphPolarizationPowers

/-! # Segre Section Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreSectionPowers

noncomputable section

/-! For a section embedding, every Presentations Segre presentation pulls native
O(m) back to the actual m-th power of the fixed product polarization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

attribute [local instance] MvPolynomial.gradedAlgebra
variable {S : Scheme.{0}} (X : Over S) (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) {n : ℕ}
  (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ P.sheaf))
  (hs : ∀ x : X.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
  (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).left)

def e34SectionPresentation : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X where
  dimension := n
  embedding := (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).left
  closed := he
  over_base := (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs).w

theorem e34SectionPresentation_coefficient :
    (e34SectionPresentation X P s hs he).coefficientEmbedding = AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism X.hom s hs :=
  pullback.lift_fst _ _ _

theorem e34SectionPresentation_hyperplane (j : Fin (n + 1)) :
    Nonempty (Presentations.PresentationFrames.PolarizationEmbedding.e34HyperplanePullback (e34SectionPresentation X P s hs he) j ≅ P.sheaf) := by
  change Nonempty ((Scheme.Modules.pullback
    (e34SectionPresentation X P s hs he).coefficientEmbedding).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j) ≅ P.sheaf)
  rw [e34SectionPresentation_coefficient]
  exact Section.HyperplanePullback.PolarizationEmbedding.exists_sectionHyperplane_pullback_iso X.hom s hs j

variable (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ X))
  (hSegre : HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation
    (e34SectionPresentation X P s hs he) (e34SectionPresentation X P s hs he) B)

include hSegre in
theorem e34SegreSection_hyperplane (j : Fin (B.dimension + 1)) :
    Nonempty ((Scheme.Modules.pullback B.coefficientEmbedding).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j) ≅ (Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34ProductLine X P).sheaf) := by
  let BA := e34SectionPresentation X P s hs he
  let H := SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) (0 : Fin (n + 1))
  obtain ⟨e⟩ := SegreHyperplaneComparison.PolarizationEmbedding.exists_segre_hyperplane_iso BA BA B hSegre j 0 0
  obtain ⟨hp⟩ := e34SectionPresentation_hyperplane X P s hs he (0 : Fin (n + 1))
  let eL := (Scheme.Modules.pullbackComp (prod.fst : X ⨯ X ⟶ X).left BA.coefficientEmbedding).symm.app H ≪≫
    (Scheme.Modules.pullback (prod.fst : X ⨯ X ⟶ X).left).mapIso hp
  let eR := (Scheme.Modules.pullbackComp (prod.snd : X ⨯ X ⟶ X).left BA.coefficientEmbedding).symm.app H ≪≫
    (Scheme.Modules.pullback (prod.snd : X ⨯ X ⟶ X).left).mapIso hp
  exact ⟨e ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr eL eR⟩

include hSegre in
theorem e34SegreSection_powers (j : Fin (B.dimension + 1)) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback B.coefficientEmbedding).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := Γ(S, ⊤)) j m) ≅
        ((Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34ProductLine X P).tensorPower m).sheaf) :=
  HyperplanePullbackPowers.PolarizationEmbedding.hyperplane_pullback_power_iso B.coefficientEmbedding (Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34ProductLine X P) j
    (e34SegreSection_hyperplane X P s hs he B hSegre j) m

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreSectionPowers

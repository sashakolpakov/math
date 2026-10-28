import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplanePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback

/-! # Hyperplane Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HyperplanePowers

noncomputable section

/-! Package the native projective hyperplane dual as a line bundle and
identify every tensor power under the section-defined embedding. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor.PolarizationAmpleness
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveHyperplaneLine (R : Type u) [CommRing R] (n : ℕ) (j : Fin (n + 1)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left where
  sheaf := SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j
  locallyTrivial x := by
    have hx : x ∈ (⨆ i : Fin (n + 1), SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) := by
      rw [SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, hi, ⟨?_⟩⟩
    exact (Scheme.Modules.restrictFunctorIsoPullback
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι).symm.app _ ≪≫
        SheafCohomology.Projective.HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j

variable {X S : Scheme.{0}} (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (f : X ⟶ S) {n : ℕ}
  (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P.sheaf))
  (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))

theorem sectionHyperplane_class (j : Fin (n + 1)) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (projectiveHyperplaneLine Γ(S, ⊤) n j)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P :=
  Quotient.sound (Section.HyperplanePullback.PolarizationEmbedding.exists_sectionHyperplane_pullback_iso f s hs j)

theorem sectionHyperplane_power_iso (j : Fin (n + 1)) (m : ℕ) :
    Nonempty ((((projectiveHyperplaneLine Γ(S, ⊤) n j).tensorPower m).pullback
      (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).sheaf ≅ (P.tensorPower m).sheaf) := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf
      (((projectiveHyperplaneLine Γ(S, ⊤) n j).tensorPower m).pullback
        (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (P.tensorPower m) := by
    change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((projectiveHyperplaneLine Γ(S, ⊤) n j).tensorPower m)) = _
    rw [AmpleTensor.PolarizationAmpleness.tensorPower_class, map_pow, sectionHyperplane_class P f s hs, AmpleTensor.PolarizationAmpleness.tensorPower_class]
  exact Quotient.exact h

theorem sectionAbsolute_closed_of_relative [IsAffine S]
    [IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left] :
    IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  let p := CategoryTheory.Limits.pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have : IsIso p := inferInstanceAs (IsIso
    (CategoryTheory.Limits.pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  have hp : (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left ≫ p = AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  exact (congrArg IsClosedImmersion hp).mp inferInstance

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HyperplanePowers

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoordinateTransitivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoCoefficientSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePrecomposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Coordinate Orbits -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CoordinateOrbits

noncomputable section

/-! A polarized isomorphism identifies complete graph-power embeddings
up to an actual invertible change of projective coordinates. This holds
over arbitrary bases, so the coordinate comparison retains nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem completePolarizedEmbeddings_coordinate_transitivity
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : Moduli.Isomorphisms.LevelPreservingIso A B) (d n : ℕ)
    (s : Fin (n + 1) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower d).sheaf))
    (t : Fin (n + 1) →
      (Line.Bundles.structureModule B.abelian.scheme.left ⟶ (B.graphBundle.tensorPower d).sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : B.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i))
    (hbs : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      A.abelian.scheme.hom.appTop.hom (A.graphBundle.tensorPower d).sheaf s))
    (hbt : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      B.abelian.scheme.hom.appTop.hom (B.graphBundle.tensorPower d).sheaf t)) :
    ∃ z : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤)),
      SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs ≫
          (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z).hom =
        e.abelian.hom ≫ SectionsProjectiveMorphism.sectionProjectiveMorphism B.abelian.scheme.hom t ht := by
  let L := A.graphBundle.tensorPower d
  let Q := B.graphBundle.tensorPower d
  let M := Q.pullback e.abelian.hom.left
  let t' := fun i => Ample.LineBundles.pullbackSection e.abelian.hom.left (t i)
  have ht' : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t' i) :=
    Section.ChartArbitraryPullback.lineBundleSections_pullback_covers e.abelian.hom.left Q t ht
  obtain ⟨b, hb⟩ := (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff
    B.abelian.scheme.hom.appTop.hom Q.sheaf t).mp hbt
  let b' := b.map (IsoCoefficientSectionBasis.sourceIsoCoefficientSectionEquiv e.abelian Q.sheaf)
  have hb' : Coefficient.RingSectionBasis.coefficientRingBasisFamily A.abelian.scheme.hom.appTop.hom M.sheaf b' = t' := by
    funext i
    exact (IsoCoefficientSectionBasis.coefficientRingBasisFamily_sourceIso e.abelian Q.sheaf b i).trans
      (congrArg (Ample.LineBundles.pullbackSection e.abelian.hom.left) (congrFun hb i))
  have hbt' : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      A.abelian.scheme.hom.appTop.hom M.sheaf t') :=
    (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff
      A.abelian.scheme.hom.appTop.hom M.sheaf t').mpr ⟨b', hb'⟩
  let φ : L.sheaf ≅ M.sheaf :=
    (B.graphBundle.powerBaseChangeIso e.abelian.hom.left d ≪≫
      (TensorPower.Maps.tensorPowerFunctor A.abelian.scheme.left d).mapIso e.graphBundleIso).symm
  let z := Section.FrameChanges.completeSectionFrameChange A.abelian.scheme.hom.appTop.hom s t' hbs hbt' φ
  refine ⟨z, ?_⟩
  exact (Section.CoordinateTransitivity.completeSectionEmbeddings_coordinate_transitivity
    A.abelian.scheme.hom L M s t' hs ht' hbs hbt' φ).trans
      (Section.ProjectivePrecomposition.sectionProjectiveMorphism_precomp e.abelian.hom Q t ht ht').symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CoordinateOrbits

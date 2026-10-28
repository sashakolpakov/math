import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ProjectivePointOrbitReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CoordinateOrbits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSectionExt
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.LevelFrameParameter

/-! # Marked Orbits -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.MarkedOrbits

noncomputable section

/-! An original polarized full-level isomorphism carries the marked
configurations of two complete graph-power embeddings into the same
linear-coordinate orbit. The coordinate change is constructed from the
complete section bases; no embedding compatibility is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem marked_coordinate_square
    {C : Type*} [Category* C] {W X Y P : C}
    (s : W ⟶ X) (t : W ⟶ Y) (p : X ⟶ P) (q : Y ⟶ P)
    (e : X ⟶ Y) (z : P ⟶ P) (v w : W ⟶ P)
    (hv : s ≫ p = v) (hw : t ≫ q = w)
    (he : s ≫ e = t) (hz : p ≫ z = e ≫ q) : v ≫ z = w := by
  rw [← hv, Category.assoc, hz, ← Category.assoc, he, hw]

theorem completePolarizedMarkedEmbeddings_frameRelated
    {S : Scheme.{u}} {g N m : ℕ} {δ : Fin g → ℕ}
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
      B.abelian.scheme.hom.appTop.hom (B.graphBundle.tensorPower d).sheaf t))
    (labels : Fin m → Multiplicative (Fin (2 * g) → ZMod N))
    (v w : Fin m → Fin (n + 1) → Γ(S, ⊤))
    (hv : ∀ a, ∀ x : S, ∃ i, x ∈ S.basicOpen (v a i))
    (hw : ∀ a, ∀ x : S, ∃ i, x ∈ S.basicOpen (w a i))
    (hsv : ∀ a,
      Over.homMk (A.abelian.fullLevelGlobalSection A.level (labels a))
        (A.abelian.fullLevelGlobalSection_comp A.level (labels a)) ≫
          SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs =
            Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (v a) (hv a))
    (htw : ∀ a,
      Over.homMk (B.abelian.fullLevelGlobalSection B.level (labels a))
        (B.abelian.fullLevelGlobalSection_comp B.level (labels a)) ≫
          SectionsProjectiveMorphism.sectionProjectiveMorphism B.abelian.scheme.hom t ht =
            Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (w a) (hw a)) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated v w := by
  obtain ⟨z, hz⟩ := CoordinateOrbits.completePolarizedEmbeddings_coordinate_transitivity
    e d n s t hs ht hbs hbt
  apply Scalar.ProjectivePointOrbitReflection.configurationFrameRelated_of_projective_coordinate_change v w hv hw z
  intro a
  let sa : Over.mk (𝟙 S) ⟶ A.abelian.scheme :=
    Over.homMk (A.abelian.fullLevelGlobalSection A.level (labels a))
      (A.abelian.fullLevelGlobalSection_comp A.level (labels a))
  let sb : Over.mk (𝟙 S) ⟶ B.abelian.scheme :=
    Over.homMk (B.abelian.fullLevelGlobalSection B.level (labels a))
      (B.abelian.fullLevelGlobalSection_comp B.level (labels a))
  have he : sa ≫ e.abelian.hom = sb := by
    apply Over.OverMorphism.ext
    exact congrArg Over.Hom.left
      (e.level (Over.mk (𝟙 S)) (LocallyConstant.const S (labels a)))
  exact marked_coordinate_square sa sb
    (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs)
    (SectionsProjectiveMorphism.sectionProjectiveMorphism B.abelian.scheme.hom t ht)
    e.abelian.hom (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z).hom
    (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (v a) (hv a))
    (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (w a) (hw a)) (hsv a) (htw a) he hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.MarkedOrbits

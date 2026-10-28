import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AmplePullbackFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle

/-! # Geometrically Ample Section Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeometricallyAmpleSectionMorphism

noncomputable section

/-! A globally generating finite family of sections of a geometrically fiberwise ample line bundle on a proper scheme defines a finite morphism to projective space over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem sectionProjectiveMorphism_isFinite_of_geometric_ample
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (hL : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S),
      (L.pullback (Limits.pullback.fst f b)).IsAmple) :
    IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left := by
  let a := SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs
  have : IsProper (a.left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom) := a.w.symm ▸ inferInstanceAs (IsProper f)
  have : IsProper a.left := IsProper.of_comp a.left (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom
  apply Relative.AmplePullbackFiniteness.proper_overMap_isFinite_of_geometric_ample_pullback a (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n)
  intro K _ _ b
  let e := RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f s hs
  exact (hL K b).of_iso ((Scheme.Modules.pullback (Limits.pullback.fst f b)).mapIso e.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeometricallyAmpleSectionMorphism

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BundleIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoIdentityBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangedSectionConstants

/-! # Bundle Iso Open Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BundleIsoOpenDescent

noncomputable section

/-! Local isomorphisms of two line bundles on a fixed projective family
glue when their fibers along a section have a specified global comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem projective_bundleIso_of_openCover
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S)
    (L M : Line.Bundles.LineBundle X.left)
    (b : (L.pullback s).sheaf ≅ (M.pullback s).sheaf)
    (C : S.OpenCover.{u})
    (hlocal : ∀ i, Nonempty
      ((L.pullback (pullback.fst X.hom (C.f i))).sheaf ≅
        (M.pullback (pullback.fst X.hom (C.f i))).sheaf)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let F := Relative.BundleIsoSheaf.relativeBundleIsoPresheaf X.hom L M
  let V : C.I₀ → Over S := fun i => Over.mk (C.f i)
  let j : ∀ i, V i ⟶ Over.mk (𝟙 S) :=
    fun i => Over.homMk (C.f i) (Category.comp_id _)
  let R := Sieve.ofArrows V j
  have hR : R ∈ (Scheme.zariskiTopology.over S) (Over.mk (𝟙 S)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact C.mem_grothendieckTopology
  have hi (i : C.I₀) : Nonempty (F.obj (.op (V i))) := by
    change Nonempty ((L.pullback (pullback.snd (C.f i) X.hom)).sheaf ≅
      (M.pullback (pullback.snd (C.f i) X.hom)).sheaf)
    have hc : Line.Bundles.LineBundle.pullbackClass (pullback.fst X.hom (C.f i)) (Line.Bundles.LineBundle.classOf L) =
        Line.Bundles.LineBundle.pullbackClass (pullback.fst X.hom (C.f i)) (Line.Bundles.LineBundle.classOf M) :=
      Quotient.sound (hlocal i)
    have h := congrArg (Line.Bundles.LineBundle.pullbackClass (pullbackSymmetry X.hom (C.f i)).inv) hc
    have he : Line.Bundles.LineBundle.classOf (L.pullback (pullback.snd (C.f i) X.hom)) =
        Line.Bundles.LineBundle.classOf (M.pullback (pullback.snd (C.f i) X.hom)) := by
      change Line.Bundles.LineBundle.pullbackClass (pullback.snd (C.f i) X.hom) (Line.Bundles.LineBundle.classOf L) =
        Line.Bundles.LineBundle.pullbackClass (pullback.snd (C.f i) X.hom) (Line.Bundles.LineBundle.classOf M)
      simpa only [← Line.Bundles.LineBundle.pullbackClass_comp, pullbackSymmetry_inv_comp_fst] using h
    exact Quotient.exact he
  have hΓ (T : Over S) :
      Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection X.hom s hs).app T).left.appTop := by
    have : IsIso (pullback.fst T.hom X.hom).appTop :=
      UniversalGlobalFunctions.projectivePresentation_baseChange_globalFunctions_isIso P s hs
        (IsPullback.of_hasPullback T.hom X.hom).flip
    have : IsIso ((Section.BaseChangeFunctor.familyBaseChangeSection X.hom s hs).app T).left.appTop :=
      Proper.FieldBaseChangeConstants.section_globalFunctions_isIso (pullback.fst T.hom X.hom)
        ((Section.BaseChangeFunctor.familyBaseChangeSection X.hom s hs).app T).left
        (Section.BaseChangeFunctor.familyBaseChangeSection_fst X.hom s hs T)
    exact ConcreteCategory.bijective_of_isIso _
  apply (IsoIdentityBaseChange.relativeBundleIso_identity_nonempty_iff X.hom L M).mp
  apply Normalized.BundleIsoDescent.relativeBundleIso_nonempty_of_cover X.hom s hs L M b Scheme.zariskiTopology
    hΓ (Over.mk (𝟙 S)) R hR
  intro T f hf
  obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff V j f).mp hf
  exact (hi i).map (F.map a.op)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BundleIsoOpenDescent

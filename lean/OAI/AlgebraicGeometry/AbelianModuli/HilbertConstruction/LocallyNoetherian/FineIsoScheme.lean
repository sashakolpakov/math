import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IsoOpenChart
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalOpenChartsCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentability
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FamilyLevelIsoSheaf

/-! # Fine Iso Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FineIsoScheme

noncomputable section

/-! The complete polarized-isomorphism functor of two fixed locally Noetherian families at full level at least three is represented on all test schemes by an actual scheme, constructed by gluing its local quasi-projective parameters. Its structure morphism is a monomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem locallyNoetherian_polarizedIso_scheme_representation
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) :
    ∃ M : Over S, Nonempty (Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj M) ∧ Mono M.hom := by
  let C := fun x : S => Polarized.IsoOpenChart.polarizedIsoOpenChart A B hδ hN x
  have hcover : ∀ x : S, ∃ a y, (C a).inclusion y = x := by
    intro x
    obtain ⟨y, hy⟩ := (C x).covers
    exact ⟨x, y, hy⟩
  have hs : ∀ T : Over S, Subsingleton ((Family.LevelIsoFunctor.familyLevelIsoFunctor A B).obj (.op T)) :=
    UniversalLevelRigidity.polarizedPullbackIsomorphisms_subsingleton_of_locallyNoetherian A B hN
  have hsurj : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (Sigma.desc (fun x : S => (C x).toFunctor)) :=
    SubterminalOpenChartsCover.restrictedRepresentedCharts_locallySurjective (Family.LevelIsoFunctor.familyLevelIsoFunctor A B) hs
      (fun x => (C x).base) (fun x => (C x).inclusion) (fun x => (C x).openImmersion) hcover
      (fun x => (C x).parameter) (fun x => (C x).representation)
  let hopen := fun x : S => (C x).toFunctor_isOpenImmersion hN
  let M := Relative.LocalRepresentationSection.relativeLocalRepresentationScheme hopen
  let e : Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj M :=
    Relative.LocalRepresentability.relativeLocalRepresentationIso hopen (FamilyLevelIsoSheaf.familyLevelIsoFunctor_isSheaf_locallyNoetherian A B hδ)
  exact ⟨M, ⟨e⟩, RepresentedIsoMonomorphism.representedPolarizedIsoParameter_mono A B hN M e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FineIsoScheme

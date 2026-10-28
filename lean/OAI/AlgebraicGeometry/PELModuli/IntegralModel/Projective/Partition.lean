import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ProjectiveComponentCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexClosedImageDisjointness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointOpenCoverFinite
import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts

/-! # Partition -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.Partition

noncomputable section

section

/-! The actual projective components in ReferenceFamily give a finite disjoint
scheme decomposition of the reduced complex reference. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (κ : K →+* ℂ)

omit [NumberField K] in
theorem reduced_projective_component_partition
    [LocallyOfFiniteType (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom] [CompactSpace (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left]
    (hM : M.HasProjectiveBallComponents κ) :
    Finite (M.ComplexComponent κ) ∧
      ∃ V : M.ComplexComponent κ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety,
        ∃ f : ∀ c, (V c).toOver ⟶ Reduced.ReducedComplexPEL.reducedComplexPEL M κ,
          (∀ c, IsOpenImmersion (f c).left ∧ IsClosedImmersion (f c).left) ∧
          Pairwise (fun c d => Disjoint (Set.range (f c).left) (Set.range (f d).left)) ∧
          (⋃ c, Set.range (f c).left) = Set.univ ∧
          IsIso (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc f).left := by
  obtain ⟨V, f, hf, hlabels, hcover⟩ := Reduced.ProjectiveComponentCover.reduced_projective_component_cover M κ hM
  have (c : M.ComplexComponent κ) : IsOpenImmersion (f c).left := (hf c).2.1
  have (c : M.ComplexComponent κ) : IsClosedImmersion (f c).left := (hf c).2.2
  have (c : M.ComplexComponent κ) : LocallyOfFiniteType (V c).toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType (V c).structureMap)
  have (c : M.ComplexComponent κ) : Nonempty (V c).toOver.left := (V c).carrier_nonempty
  have hd : Pairwise (fun c d => Disjoint (Set.range (f c).left) (Set.range (f d).left)) := by
    intro c d hcd
    apply ComplexClosedImageDisjointness.closed_complex_images_disjoint (f c) (f d)
    intro y z h
    have hc : ConnectedComponents.mk (y ≫ (f c ≫ Reduced.ReducedComplexPEL.reducedComplexPELInclusion M κ)) = c := by
      apply (hlabels c).le
      exact ⟨y, rfl⟩
    have hd : ConnectedComponents.mk (z ≫ (f d ≫ Reduced.ReducedComplexPEL.reducedComplexPELInclusion M κ)) = d := by
      apply (hlabels d).le
      exact ⟨z, rfl⟩
    have he := congrArg (fun a => ConnectedComponents.mk (a ≫ Reduced.ReducedComplexPEL.reducedComplexPELInclusion M κ)) h
    simp only [Category.assoc] at he
    exact hcd (hc.symm.trans (he.trans hd))
  have hfinite := DisjointOpenCoverFinite.disjoint_open_cover_finite (fun c => (V c).toOver.left) (fun c => (f c).left) hd hcover
  exact ⟨hfinite, V, f, (fun c => ⟨inferInstance, inferInstance⟩), hd, hcover,
    DisjointOpenCoverFinite.disjoint_open_cover_sigma_isIso (fun c => (V c).toOver.left) (fun c => (f c).left) hd hcover⟩

end

/-! Smoothness and properness of an actual finite coproduct of the
smooth projective varieties appearing in ReferenceFamily. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem projective_partition_smooth_proper {I : Type} [Finite I]
    (V : I → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : ∀ i, (V i).toOver ⟶ X) [IsIso (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc f).left] :
    Smooth X.hom ∧ IsProper X.hom := by
  let : IsZariskiLocalAtSource (@Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  let : MorphismProperty.RespectsIso (@Smooth.{0}) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Smooth.{0})]
    exact affineLocally_respectsIso RingHom.Smooth RingHom.Smooth.propertyIsLocal.respectsIso
  let q := ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc f
  have hs : Smooth (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigma (fun i => (V i).toOver)).hom :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0})
      (fun i => inferInstanceAs (Smooth (V i).structureMap))
  have hp : IsProper (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigma (fun i => (V i).toOver)).hom :=
    ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.proper_finite_sigma_desc ℂ (fun i => (V i).structureMap)
      (fun i => inferInstance)
  constructor
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{0}) q.left, q.w]
    exact hs
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) q.left, q.w]
    exact hp

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.Partition

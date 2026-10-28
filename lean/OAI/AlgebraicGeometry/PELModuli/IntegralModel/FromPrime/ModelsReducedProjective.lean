import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ReducedFineFiniteType
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.Partition
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PartitionAffine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PartitionPresentation

/-! # Models Reduced Projective -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedProjective.FromPrimeModels

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem reduced_projectivePEL_complex_geometry
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] (κ : K →+* ℂ)
    {s N : ℕ} [NeZero N] (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hs : 0 < s)
    (hδ : ∀ i, 0 < P.polarizationType i)
    (hchain : ∀ i j, i ≤ j → P.polarizationType i ∣ P.polarizationType j)
    (iota : E →+* K) (hN : 3 ≤ N) (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
    (hproj : M.HasProjectiveBallComponents κ)
     (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    IsNoetherian (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left ∧
      Smooth (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom ∧ IsProper (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom ∧
      Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left
        (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Reduced.ReducedComplexPEL.reducedComplexPEL M κ)) ∧
      Finite (M.ComplexComponent κ) ∧
      (∀ (F : Set (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left), F.Finite →
        ∃ U : (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left.Opens, IsAffineOpen U ∧ F ⊆ U) := by
  obtain ⟨hft, hqc, _⟩ := ReducedFineFiniteType.FromPrimeModels.reduced_finePEL_finiteness κ P hs hδ hchain iota hN M hM hPresentations
  have : LocallyOfFiniteType (Reduction.reduction M.space).hom := hft
  have : QuasiCompact (Reduction.reduction M.space).hom := hqc
  have : LocallyOfFiniteType (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (Reduction.reduction M.space).hom
      (Spec.map (CommRingCat.ofHom κ))))
  have : QuasiCompact (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd (Reduction.reduction M.space).hom
      (Spec.map (CommRingCat.ofHom κ))))
  have : IsLocallyNoetherian (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom
  have : CompactSpace (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left :=
    QuasiCompact.compactSpace_of_compactSpace (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom
  obtain ⟨hfinite, V, f, hf, hd, hcover, hiso⟩ := Projective.Partition.reduced_projective_component_partition M κ hproj
  have : Finite (M.ComplexComponent κ) := hfinite
  have : IsIso (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc f).left := hiso
  obtain ⟨hsmooth, hproper⟩ := Projective.Partition.projective_partition_smooth_proper V f
  obtain ⟨p⟩ := Projective.PartitionPresentation.projective_partition_native_presentation V f
  refine ⟨⟨⟩, hsmooth, hproper, ⟨p⟩, Projective.PartitionPresentation.native_projective_relative_presentation p, hfinite, ?_⟩
  intro F hF
  exact @Projective.PartitionAffine.projective_partition_finite_set_affine (M.ComplexComponent κ) hfinite V
    (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left (fun c => (f c).left) (fun c => (hf c).1) hd hcover F hF

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedProjective.FromPrimeModels

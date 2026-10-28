import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationQuotient

/-! # Killed Translation Kernel Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KilledTranslationKernelQuotient

noncomputable section

/-! An invertible exponent killing the actual translation kernel places
it inside finite etale torsion. Its original specialization property
makes an etale kernel finite and supplies the unchanged quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

local instance killedKernel_sourceNoetherian : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

local instance killedKernel_group : GrpObj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :=
  (Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup A L P).group

local instance killedKernel_commutative : IsCommMonObj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :=
  Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup_commutative A L P

local instance killedKernel_inclusionMonHom : IsMonHom (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) :=
  Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroInclusion_isMonHom A L P

omit [IsAffine S] in
theorem killedTranslationKernel_formallyUnramified
    (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x))
    (hi : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P ^ n = 1) :
    FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let T := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A.scheme n
  let t := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A.scheme n
  let j : Z ⟶ T := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n i hi
  have hj : j.left ≫ t.left = i.left :=
    congrArg Over.Hom.left (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n i hi)
  have : Mono i.left :=
    Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_left_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  have : Mono j.left := mono_of_mono_fac hj
  have : Etale T.hom := AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_etale A.scheme n hn
  have h : FormallyUnramified (j.left ≫ T.hom) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
  exact j.w ▸ h

theorem killedTranslationKernel_isFinite
    (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x))
    (hi : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P ^ n = 1)
    [Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom] :
    IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let T := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A.scheme n
  let t := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A.scheme n
  let j : Z ⟶ T := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n i hi
  have hj : j ≫ t = i := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n i hi
  have hj' : j.left ≫ t.left = i.left := congrArg Over.Hom.left hj
  obtain ⟨hfin, het⟩ := AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A.scheme n hn
  let : IsFinite T.hom := hfin
  let : Etale T.hom := het
  let : IsClosedImmersion t.left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.torsion_closedImmersion A.scheme n
  let : Mono i.left :=
    Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_left_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  let : Mono j.left := mono_of_mono_fac hj'
  let : Etale (j.left ≫ T.hom) := by rw [j.w]; infer_instance
  let : Etale j.left := Etale.of_comp j.left T.hom
  let : IsOpenImmersion j.left := IsOpenImmersion.of_flat_of_mono j.left
  have hs : StableUnderSpecialization (Set.range i.left) := by
    change StableUnderSpecialization
      (Set.range (Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P).hom)
    simpa only [Category.comp_id] using
      Picard.ThetaConstruction.RelativeSpecialization.Geometric.RelativeRigidifiedCharts.zeroProjection_range_stableUnderSpecialization P
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) (𝟙 A.scheme.left)
  have hs' : StableUnderSpecialization (Set.range j.left) := by
    intro x y hxy hx
    obtain ⟨z, hz⟩ := hx
    have hx' : t.left x ∈ Set.range i.left :=
      ⟨z, (congrArg (fun b : Z.left ⟶ A.scheme.left => b z) hj').symm.trans
        (congrArg t.left hz)⟩
    obtain ⟨w, hw⟩ := hs (hxy.map t.left.continuous) hx'
    refine ⟨w, t.left.isClosedEmbedding.injective ?_⟩
    exact (congrArg (fun b : Z.left ⟶ A.scheme.left => b w) hj').trans hw
  let : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  let : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  let : IsNoetherian T.left := ⟨⟩
  have hclosed : IsClosed (Set.range j.left) :=
    Picard.ThetaConstruction.NoetherianSpecializationClosed.Geometric.isClosed_of_isOpen_stableUnderSpecialization j.left.isOpenEmbedding.isOpen_range hs'
  let : IsClosedImmersion j.left := IsClosedImmersion.of_isPreimmersion j.left hclosed
  have h : IsFinite (j.left ≫ T.hom) := inferInstance
  exact j.w ▸ h

theorem killedTranslationKernel_inclusion_closedImmersion
    (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x))
    (hi : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P ^ n = 1)
    [Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom] :
    IsClosedImmersion (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P).left := by
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  have : IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom :=
    killedTranslationKernel_isFinite A L P n hn hi
  have : IsFinite (i.left ≫ A.scheme.hom) := by rw [i.w]; infer_instance
  have : IsFinite i.left := IsFinite.of_comp i.left A.scheme.hom
  have : Mono i.left :=
    Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_left_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  exact (IsClosedImmersion.iff_isFinite_and_mono i.left).mpr ⟨inferInstance, inferInstance⟩

theorem ampleTranslationQuotient_nonempty_of_killed
    (n : ℕ) (hn : 0 < n) (hunit : ∀ x : S, IsUnit (n : S.presheaf.stalk x))
    (hi : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P ^ n = 1)
    [Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom] :
    Nonempty (Ample.TranslationQuotient.AmpleTranslationQuotient A L P) := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  have : IsFinite Z.hom := killedTranslationKernel_isFinite A L P n hunit hi
  obtain ⟨B, f, r, he, hr, hfr, hrf, hk, hu⟩ := AbelianScheme.IsogenyQuotient.Finite.EtaleGroup.Construction.finiteEtaleGroupQuotient_exists A Z i
    (killedTranslationKernel_inclusion_closedImmersion A L P n hunit hi) n hi
  exact ⟨⟨n, hn, B, f, r, he, hr, hfr, hrf, hk, hu⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KilledTranslationKernelQuotient

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.TranslationKernelEtale
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.UnramifiedGroupExponent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeSpecialization
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianSpecializationClosed

/-! # Translation Kernel Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.TranslationKernelFinite

noncomputable section

/-! The ample translation kernel is finite over an affine Noetherian
rational base. A uniform exponent places it inside actual finite torsion;
its open image is closed by specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianSpecializationClosed.Geometric

variable {S : Scheme} [hS : IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (qS : S ⟶ Spec (.of ℚ)) (A : Abelian.Schemes.AbelianScheme g S)
    (L : Line.Bundles.LineBundle A.scheme.left) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

local instance rationalKernelFiniteSource_locallyNoetherian : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

local instance rationalKernel_group : GrpObj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :=
  (Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup A L P).group

local instance rationalKernel_commutative : IsCommMonObj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :=
  Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup_commutative A L P

local instance rationalKernel_inclusion_isMonHom : IsMonHom (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) :=
  Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroInclusion_isMonHom A L P

include hS qS

theorem rationalTranslationKernel_exists_exponent (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧
      (𝟙 (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :
        Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P ⟶ Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) ^ n = 1 := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let : Etale Z.hom := TranslationKernelEtale.rationalTranslationKernel_etale qS A L P hL
  let : QuasiCompact Z.hom := by
    change QuasiCompact ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P).hom ≫
      A.scheme.hom)
    infer_instance
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  apply Uniform.UnramifiedGroupExponent.quasiCompact_unramifiedGroup_exists_exponent Z
  intro k _ _ s a
  let G := (Over.pullback s).obj Z
  let : GrpObj G := Functor.grpObjObj
  let : IsCommMonObj G := Functor.isCommMonObj_obj (F := Over.pullback s) (M := Z)
  let : IsFinite G.hom := TranslationKernelEtale.ampleTranslationKernel_geometric_isFinite A L P hL s
  obtain ⟨n, hn, hkill⟩ := FormalGeometry.Completion.Finite.GroupAnnihilator.Construction.finiteGroup_exists_annihilator k (Grp.mk G)
  let U : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  let e₀ : Over.mk s ≅ (Over.map s).obj U := Over.isoMk (Iso.refl (Spec (.of k))) (by simp [U])
  let a' := e₀.inv ≫ a
  let e := Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsMulEquiv Z s U
  have ha' : a' ^ n = 1 := by
    have h := congrArg e (hkill U (e.symm a'))
    simpa only [map_pow, map_one, MulEquiv.apply_symm_apply] using h
  have hea : e₀.hom ≫ a' = a := by simp [a']
  refine ⟨n, hn, ?_⟩
  have h := congrArg (fun b => e₀.hom ≫ b) ha'
  simpa only [MonObj.comp_pow, MonObj.comp_one, hea] using h

theorem rationalTranslationKernel_isFinite (hL : L.IsAmple) :
    IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let : Etale Z.hom := TranslationKernelEtale.rationalTranslationKernel_etale qS A L P hL
  obtain ⟨n, hn, hkill⟩ := rationalTranslationKernel_exists_exponent qS A L P hL
  have hi : i ^ n = 1 := by
    have h := congrArg (fun b => b ≫ i) hkill
    simpa only [MonObj.pow_comp, MonObj.one_comp, Category.id_comp] using h
  let T := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A.scheme n
  let t := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A.scheme n
  let j : Z ⟶ T := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n i hi
  have hj : j ≫ t = i := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n i hi
  have hj' : j.left ≫ t.left = i.left := congrArg Over.Hom.left hj
  obtain ⟨hfin, het⟩ := AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A.scheme n
    (AbelianScheme.IsogenyQuotient.Unit.Construction.positive_integer_unit_on_characteristic_zero_base qS n hn)
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

theorem rationalTranslationKernel_inclusion_closedImmersion (hL : L.IsAmple) :
    IsClosedImmersion (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P).left := by
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let : IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom :=
    rationalTranslationKernel_isFinite qS A L P hL
  let : IsFinite (i.left ≫ A.scheme.hom) := by rw [i.w]; infer_instance
  let : IsFinite i.left := IsFinite.of_comp i.left A.scheme.hom
  let : Mono i.left :=
    Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_left_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  exact (IsClosedImmersion.iff_isFinite_and_mono i.left).mpr ⟨inferInstance, inferInstance⟩

theorem rationalTranslationKernel_finite_etale (hL : L.IsAmple) :
    IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom ∧
      Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom :=
  ⟨rationalTranslationKernel_isFinite qS A L P hL,
    TranslationKernelEtale.rationalTranslationKernel_etale qS A L P hL⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.TranslationKernelFinite

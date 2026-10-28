import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationQuotient

/-! # Etale Translation Kernel Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.EtaleTranslationKernelQuotient

noncomputable section

/-! A finite etale actual translation kernel has a uniform positive
annihilator and the original effective quotient, with no invertibility
requirement on the annihilator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

local instance finiteEtaleKernel_sourceNoetherian : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
local instance finiteEtaleKernel_group : GrpObj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :=
  (Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup A L P).group
local instance finiteEtaleKernel_commutative : IsCommMonObj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :=
  Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup_commutative A L P
local instance finiteEtaleKernel_inclusionMonHom : IsMonHom (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) :=
  Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroInclusion_isMonHom A L P

theorem finiteEtaleTranslationKernel_exists_exponent
    [IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom]
    [Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom] :
    ∃ n : ℕ, 0 < n ∧
      (𝟙 (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) :
        Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P ⟶ Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) ^ n = 1 := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  apply Uniform.UnramifiedGroupExponent.quasiCompact_unramifiedGroup_exists_exponent Z
  intro k _ _ s a
  let G := (Over.pullback s).obj Z
  let : GrpObj G := Functor.grpObjObj
  let : IsCommMonObj G := Functor.isCommMonObj_obj (F := Over.pullback s) (M := Z)
  let : IsFinite G.hom := inferInstanceAs (IsFinite (Limits.pullback.snd Z.hom s))
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

theorem ampleTranslationQuotient_nonempty_of_finite_etale
    [IsFinite (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom]
    [Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom] :
    Nonempty (Ample.TranslationQuotient.AmpleTranslationQuotient A L P) := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  obtain ⟨n, hn, hkill⟩ := finiteEtaleTranslationKernel_exists_exponent A L P
  have hi : i ^ n = 1 := by
    have h := congrArg (fun b => b ≫ i) hkill
    simpa only [MonObj.pow_comp, MonObj.one_comp, Category.id_comp] using h
  have : IsFinite (i.left ≫ A.scheme.hom) := by rw [i.w]; infer_instance
  have : IsFinite i.left := IsFinite.of_comp i.left A.scheme.hom
  have : Mono i.left :=
    Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_left_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  have hic : IsClosedImmersion i.left :=
    (IsClosedImmersion.iff_isFinite_and_mono i.left).mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨B, f, r, he, hr, hfr, hrf, hk, hu⟩ := AbelianScheme.IsogenyQuotient.Finite.EtaleGroup.Construction.finiteEtaleGroupQuotient_exists A Z i hic n hi
  exact ⟨⟨n, hn, B, f, r, he, hr, hfr, hrf, hk, hu⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.EtaleTranslationKernelQuotient

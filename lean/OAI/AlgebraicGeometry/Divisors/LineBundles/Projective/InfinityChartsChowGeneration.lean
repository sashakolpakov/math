import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationOnClosed
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveChartGeneration
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GenerationLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveInfinityChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelativeBaseChangeChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowExtension

/-! # Infinity Charts Chow Generation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.InfinityChartsChowGeneration.BundleCycles

noncomputable section

section

/-! Noetherian induction globalizes the actual finite free
projective Chow generators across arbitrary base changes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {E X Y : Scheme.{0}} (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (H : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

include H in
theorem projectiveGenerationOnClosed_step (S : Closeds Y)
    (ih : ∀ T : Closeds Y, T < S → GenerationOnClosed.BundleCycles.ProjectiveGenerationOnClosed p L r hp T) :
    GenerationOnClosed.BundleCycles.ProjectiveGenerationOnClosed p L r hp S := by
  intro Z _ _ iZ _ hiZ b f _ d α
  cases isEmpty_or_nonempty Z with
  | inl hz =>
    let := hz
    let : IsEmpty (pullback p b : Scheme) := ⟨fun a => isEmptyElim (pullback.snd p b a)⟩
    rw [AffineBundle.ChowExtension.Cycles.dimensionChow_eq_zero_of_isEmpty (pullback.snd p b ≫ f) d α]
    exact Submodule.zero_mem _
  | inr hn =>
    let z : Z := Classical.choice hn
    obtain ⟨C⟩ := H (b z)
    let R := C.coefficient
    let M := C.module
    let : Module.Finite R M := Module.Finite.of_basis C.basis
    let q := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)
    let : Smooth q := (Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_sourceCharts C.basis).forget.smooth
    let : GeometricallyIntegral q := Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_geometricallyIntegral C.basis
    let U := pullback b C.baseMap
    let iU : U ⟶ Z := pullback.fst b C.baseMap
    let c : U ⟶ Spec R := pullback.snd b C.baseMap
    let : IsOpenImmersion iU := inferInstanceAs (IsOpenImmersion (pullback.fst b C.baseMap))
    let : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian iU
    let : U.IsSeparated := ⟨by rw [← terminal.comp_from iU]; infer_instance⟩
    obtain ⟨a, ha⟩ := C.contains
    obtain ⟨u, hu, _⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback b C.baseMap) z a ha.symm
    have hz : z ∈ Set.range iU := ⟨u, hu⟩
    let p' := pullback.snd p b
    let qU := pullback.snd q c
    let jU := Open.RelativeBaseChangeChart.BundleCycles.openRelativeBaseChangeChartMap p q C.baseMap C.totalMap C.square b
    have hsU : IsPullback qU jU iU p' :=
      Open.RelativeBaseChangeChart.BundleCycles.openRelativeBaseChangeChart_projection_isPullback p q C.baseMap C.totalMap C.square b
    have hU : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank qU r := (hp.baseChange b).of_isPullback qU iU jU hsU
    let L' := L.pullback (pullback.fst p b)
    let e := LineBundle.PullbackIso.Cycles.lineBundlePullbackSquareIso L (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
      (pullback.fst p b) C.totalMap jU (pullback.fst q c)
      (Open.RelativeBaseChangeChart.BundleCycles.openRelativeBaseChangeChartMap_fst p q C.baseMap C.totalMap C.square b) C.idealIso
    have gU (m : ℕ) (β : DimensionChow.BundleCycles.DimensionChowQ (qU ≫ (iU ≫ f)) m) :
        β ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated qU (iU ≫ f) r hU (L'.pullback jU) m :=
      Free.ProjectiveChartGeneration.BundleCycles.freeProjectiveChart_chow_generated p' L' C.basis c iU jU hsU e f r (hp.baseChange b) u m β
    let K := Open.ClosedComplement.BundleCycles.openComplementScheme iU
    let k : K ⟶ Z := Open.ClosedComplement.BundleCycles.openComplementInclusion iU
    let : IsClosedImmersion k := Open.ClosedComplement.BundleCycles.openComplementInclusion_isClosedImmersion iU
    let : AlgebraicGeometry.IsNoetherian K := Open.ClosedComplement.BundleCycles.openComplementScheme_isNoetherian iU
    let : K.IsSeparated := ⟨by rw [← terminal.comp_from k]; infer_instance⟩
    let qK := pullback.snd p' k
    let jK := pullback.fst p' k
    have gKbase := ih (Closed.ComplementInduction.BundleCycles.openComplementImageClosed iZ iU) (Closed.ComplementInduction.BundleCycles.openComplementImageClosed_lt iZ iU S hiZ z hz)
    have gKcanonical : ∀ m (β : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd p (k ≫ b) ≫ (k ≫ f)) m),
        β ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd p (k ≫ b)) (k ≫ f) r (hp.baseChange (k ≫ b))
          (L.pullback (pullback.fst p (k ≫ b))) m :=
      gKbase K (k ≫ iZ) rfl (k ≫ b) (k ≫ f)
    have gK (m : ℕ) (β : DimensionChow.BundleCycles.DimensionChowQ (qK ≫ (k ≫ f)) m) :
        β ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated qK (k ≫ f) r ((hp.baseChange b).baseChange k) (L'.pullback jK) m :=
      GenerationIso.BundleCycles.projectiveChowGeneration_iteratedBaseChange p b k (k ≫ f) r hp L gKcanonical m β
    exact ProjectiveChow.GenerationLocalization.BundleCycles.projectiveChowGeneration_of_open_closed p' qU qK iU jU k jK hsU
      (IsPullback.of_hasPullback p' k).flip (Open.ClosedComplement.BundleCycles.openComplementInclusion_range iU) f r (hp.baseChange b)
      hU ((hp.baseChange b).baseChange k) L' gU gK d α

include H in
theorem projectiveGenerationOnClosed_all [AlgebraicGeometry.IsNoetherian Y] (S : Closeds Y) :
    GenerationOnClosed.BundleCycles.ProjectiveGenerationOnClosed p L r hp S :=
  wellFounded_lt.induction S (projectiveGenerationOnClosed_step p L H r hp)

end

/-! Every genuine Chow class in a bundle with actual free infinity
charts is generated by hyperplane powers, before and after base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {E X : Scheme.{0}} (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (H : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

include H in
theorem freeInfinityCharts_baseChange_generated {Y : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (b : Y ⟶ X) (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd p b ≫ f) d) :
    α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd p b) f r (hp.baseChange b) (L.pullback (pullback.fst p b)) d := by
  have h := projectiveGenerationOnClosed_all (Y := Y) p L H r hp ⊤
  apply h Y (𝟙 Y) ?_ b f d α
  ext y
  constructor
  · intro _; trivial
  · intro _; exact ⟨y, rfl⟩

include H in
theorem freeInfinityCharts_chow_generated [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) : α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated p f r hp L d := by
  let q := pullback.snd p (𝟙 X)
  let j := pullback.fst p (𝟙 X)
  have hj : j ≫ p = q := (pullback.condition (f := p) (g := 𝟙 X)).trans (Category.comp_id _)
  exact GenerationIso.BundleCycles.projectiveChowGeneration_of_iso p q j hj f r hp (hp.baseChange (𝟙 X)) L (L.pullback j)
    (Iso.refl _) (freeInfinityCharts_baseChange_generated p L H r hp (𝟙 X) f) d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.InfinityChartsChowGeneration.BundleCycles

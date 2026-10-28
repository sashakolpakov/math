import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiscreteStalkSectionCount
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkSupportTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoherentSupportCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentCohomology

/-! # Support Stalk Euler Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SupportStalkEulerBound

noncomputable section

/-! Any finite set of nonzero stalks of a coherent sheaf with finite
support on a proper field scheme has cardinality at most its Euler
characteristic. This counts actual sheaf contributions and retains
nilpotent multiplicity. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem finiteSupport_nonzeroStalk_count_le_euler
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hf : ((Coherent.Annihilator.coherentAnnihilator M).support : Set X).Finite)
    (S : Finset X) (hS : ∀ x ∈ S, ¬ IsZero ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor x).obj M)) :
    (S.card : ℤ) ≤ CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M := by
  classical
  let I := Coherent.Annihilator.coherentAnnihilator M
  let j := I.subschemeι
  let q := j ≫ p
  let : IsFinite q := CoherentSupportCohomology.idealSubscheme_finite_of_finite_support p I hf
  let : IsLocallyArtinian I.subscheme := IsLocallyArtinian.of_locallyQuasiFinite q
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace q
  let : IsArtinianScheme I.subscheme := ⟨⟩
  obtain ⟨N, hNq, hNt, ⟨e⟩⟩ := Coherent.ClosedDescent.exists_coherent_on_annihilating_subscheme M I le_rfl
  let := hNq
  let := hNt
  have hΓN : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor q).obj N) := by
    have := Proper.CoherentCohomology.proper_coherent_cohomologyFinite q N 0
    exact Module.Finite.equiv
      (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap q) N)
  let := hΓN
  have hlift (x : S) : ∃ z : I.subscheme, j z = x.val := by
    have hx := HilbertConstruction.Module.StalkSupportTransport.nonzero_moduleStalk_mem_coherent_support M x.val (hS x.val x.property)
    have hr : x.val ∈ Set.range j := by rw [I.range_subschemeι]; exact hx
    exact hr
  choose z hz using hlift
  have hinj : Function.Injective z := by
    intro a b hab
    apply Subtype.ext
    exact (hz a).symm.trans ((congrArg j hab).trans (hz b))
  let T : Finset I.subscheme := Finset.univ.image z
  have hcard : T.card = S.card := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  have hT : ∀ y ∈ T, ¬ IsZero ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor y).obj N) := by
    intro y hy hzero
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    have hpush : IsZero ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor (j (z x))).obj ((pushforward j).obj N)) :=
      (HilbertConstruction.Module.StalkSupportTransport.modulePushforward_stalk_isZero_iff j j.isEmbedding.toIsInducing N (z x)).mpr hzero
    have hM : IsZero ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor (j (z x))).obj M) :=
      ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor (j (z x))).mapIso e).isZero_iff.mp hpush
    exact hS x.val x.property ((congrArg (fun y => IsZero ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor y).obj M)) (hz x)).mp hM)
  have : Module.Finite K ((Coefficient.SectionEvaluation.coefficientSectionFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap q) ⊤).obj N) := hΓN
  have hcount := DiscreteStalkSectionCount.discrete_stalk_count_le_sectionDimension (Coefficient.ModulePresheaf.schemeCoefficientMap q) N T hT
  let eΓ : (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor q).obj N ≃ₗ[K] (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M :=
    (Coefficient.GlobalSectionsPushforward.schemeGlobalSectionsPushforwardIso j p N).symm.trans (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso p e)
  have hbound : S.card ≤ Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) := by
    rw [← hcard]
    exact hcount.trans_eq eΓ.finrank_eq
  rw [CoherentSupportCohomology.finiteSupport_coherent_euler_eq_sections p M hf]
  exact_mod_cast hbound

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SupportStalkEulerBound

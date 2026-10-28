import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelAllDegreeVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatCochainSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseCoverVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap

/-! # Fiberwise Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberwiseVanishing

noncomputable section

/-! Vanishing on every field fiber of a proper flat line-bundle family
implies vanishing on its total space. Finite projective models prove the
affine statement, and the original affine-open Cech cover globalizes it. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem lineBundle_fieldCartesian_cohomology_vanish
    {X S Y : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X)
    (s : Spec (.of K) ⟶ S) {a : Y ⟶ X} {b : Y ⟶ Spec (.of K)}
    (H : IsPullback a b f s) (q : ℕ)
    (hzero : Subsingleton
      (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (pullback.fst f s)).sheaf q)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf q) := by
  let e := H.isoPullback
  let N := L.pullback (pullback.fst f s)
  have : IsProper (pullback.snd f s) := inferInstance
  have : (pullback f s).IsSeparated := by
    constructor
    rw [← terminal.comp_from (pullback.snd f s)]
    infer_instance
  let eN : (N.pullback e.hom).sheaf ≅ (L.pullback a).sheaf :=
    (Scheme.Modules.pullbackComp e.hom (pullback.fst f s)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr H.isoPullback_hom_fst).app L.sheaf
  let c := CohomologyPullbackIso.lineBundleCohomologyPullbackIso e.hom (pullback.snd f s) N q
  have hc : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (N.pullback e.hom).sheaf q) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective c.hom).mp inferInstance
      (hzero.elim _ _)⟩
  let d := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor Y q).mapIso eN
  exact ⟨fun x y => (AddCommGrpCat.mono_iff_injective d.inv).mp inferInstance
    (hc.elim _ _)⟩

theorem properFlat_affine_cohomology_vanish_of_field_fibers
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    (hfield : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S) (q : ℕ),
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (pullback.fst f s)).sheaf q))
    (q : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf q) := by
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from f]
    infer_instance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨k, V, ha, he, hcover⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin k) → X.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hUa : ∀ i, IsAffineOpen (U i) := fun i => ha i.down
  have hUe : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
      Line.Bundles.structureModule (U i).toScheme) := fun i => he i.down
  obtain ⟨C, φ, hφ, _, hfin, hproj, ht⟩ :=
    FiniteCechModel.properFlat_exists_finite_projective_cech_model f L U hU hUa
  have : QuasiIso φ := hφ
  have hflat (n : ℕ) : Module.Flat Γ(S, ⊤) (C.X n) := by
    have : Module.Projective Γ(S, ⊤) (C.X n) := hproj n
    infer_instance
  have hsupport : Cochain.FieldSupport.CochainFieldSupport C ⊤ := by
    intro K _ _ _ n
    let R := Γ(S, ⊤)
    let alg : Algebra R K := inferInstance
    let s : Spec (.of K) ⟶ S := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R K)
    have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap s).toAlgebra = alg := by
      rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
      exact toAlgebra_algebraMap
    have hn : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R K).mapHomologicalComplex
        (.up ℕ)).obj C).ExactAt n := by
      let P (a : Algebra R K) : Prop :=
        letI : Algebra R K := a
        letI : Module R K := Algebra.toModule
        (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R K).mapHomologicalComplex
          (.up ℕ)).obj C).ExactAt n
      have h : P (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap s).toAlgebra :=
        HilbertConstruction.Spec.ModelAllDegreeVanishing.spec_model_exactAt_of_cohomology_zero_all (IsPullback.of_hasPullback f s)
          L U hU hUa hUe φ ht n (hfield K s n)
      exact (congrArg P hAlg).mp h
    exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor C n).mp hn
  have hs := Finite.FlatCochainSupport.finiteFlatCochain_fieldSupport_homology_support C hfin hflat ⊤ hsupport q
  have hz : Module.support Γ(S, ⊤) (C.homology q) = ∅ := by
    apply Set.subset_empty_iff.mp
    change Module.support Γ(S, ⊤) (C.homology q) ⊆
      PrimeSpectrum.zeroLocus (Set.univ : Set Γ(S, ⊤)) at hs
    simpa only [PrimeSpectrum.zeroLocus_univ] using hs
  have : Subsingleton (C.homology q) :=
    (Module.support_eq_empty_iff (R := Γ(S, ⊤)) (M := C.homology q)).mp hz
  let e : C.homology q ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom q).obj L.sheaf :=
    asIso (HomologicalComplex.homologyMap φ q) ≪≫
      OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso f.appTop.hom L.sheaf U hU hUa q
  exact ModuleCat.subsingleton_of_isZero
    ((ModuleCat.isZero_of_subsingleton (C.homology q)).of_iso e.symm)

theorem properFlat_cohomology_vanish_of_field_fibers
    {X S : Scheme.{u}} [S.IsSeparated] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    (hfield : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S) (q : ℕ),
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (pullback.fst f s)).sheaf q))
    (q : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf q) := by
  apply Affine.BaseCoverVanishing.cohomology_vanish_of_affine_base_opens f L.sheaf
  intro V hV n
  have : IsAffine V.toScheme := hV
  have : IsNoetherianRing Γ(V.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V.toScheme⟩
  let W := f ⁻¹ᵁ V
  let N := L.pullback W.ι
  have H : IsPullback W.ι (f ∣_ V) f V.ι := (isPullback_morphismRestrict f V).flip
  have : IsProper (f ∣_ V) := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : Flat (f ∣_ V) := MorphismProperty.of_isPullback (P := @Flat) H inferInstance
  have hN : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N.sheaf n) := by
    apply properFlat_affine_cohomology_vanish_of_field_fibers (f ∣_ V) N
    intro K _ s r
    let a := pullback.fst (f ∣_ V) s
    let b := pullback.snd (f ∣_ V) s
    have H' : IsPullback (a ≫ W.ι) b f (s ≫ V.ι) :=
      (IsPullback.of_hasPullback (f ∣_ V) s).paste_horiz H
    have ht := lineBundle_fieldCartesian_cohomology_vanish f L (s ≫ V.ι) H' r
      (hfield K (s ≫ V.ι) r)
    let e := (Scheme.Modules.pullbackComp a W.ι).app L.sheaf
    let c := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (pullback (f ∣_ V) s) r).mapIso e
    exact ⟨fun x y => (AddCommGrpCat.mono_iff_injective c.hom).mp inferInstance
      (ht.elim _ _)⟩
  let e := (Scheme.Modules.restrictFunctorIsoPullback W.ι).app L.sheaf
  let c := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor W.toScheme n).mapIso e
  exact ⟨fun x y => (AddCommGrpCat.mono_iff_injective c.hom).mp inferInstance
    (hN.elim _ _)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberwiseVanishing

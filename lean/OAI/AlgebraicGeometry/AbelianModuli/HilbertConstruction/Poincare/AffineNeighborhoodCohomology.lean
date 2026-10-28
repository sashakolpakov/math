import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineLocalizedModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointLocalAlgebraCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineVanishing

/-! # Affine Neighborhood Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On every affine open neighborhood of the dual zero, the actual Poincare family has cohomology concentrated in degree g, equal there to the coordinate quotient by the zero point. All finite models and local comparisons are constructed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareAffine_neighborhood_cohomology_residue
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t]
    (hx : η[D.abelian.scheme].left (IsLocalRing.closedPoint K) ∈ Set.range t) :
    let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom;
    let b := pullback.snd p t;
    let L := D.poincare.pullback (pullback.fst p t);
    (∀ q : ℕ, q ≠ g → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj L.sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom g).obj L.sheaf) ≅
      ModuleCat.of Γ(T, ⊤) (Γ(T, ⊤) ⧸ D.poincareAffineParameterIdeal t)) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ D.abelian.scheme.hom)
  have : IsNoetherianRing Γ(T, ⊤) :=
    isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion T.isoSpec.inv)
  let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom
  let P := CategoryTheory.Limits.pullback p t
  let a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left := pullback.fst p t
  let b : P ⟶ T := pullback.snd p t
  let H : IsPullback a b p t := IsPullback.of_hasPullback p t
  let L := D.poincare.pullback a
  have hproper : IsProper A.abelian.scheme.hom := A.abelian.proper
  have hflat : Flat A.abelian.scheme.hom := inferInstance
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.abelian.scheme.hom).flip hproper
  have : Flat p := MorphismProperty.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.abelian.scheme.hom).flip hflat
  have : IsProper b := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : Flat b := MorphismProperty.of_isPullback (P := @Flat) H inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace b
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  obtain ⟨k, V, ha, he, hcover⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin k) → P.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hUa : ∀ i, IsAffineOpen (U i) := fun i => ha i.down
  have hUe : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
      Line.Bundles.structureModule (U i).toScheme) := fun i => he i.down
  obtain ⟨C, φ, hφ, _, hfin, hproj, ht⟩ :=
    ProperFlat.FiniteCechModel.properFlat_exists_finite_projective_cech_model b L U hU hUa
  have : QuasiIso φ := hφ
  have hf (q : ℕ) : Module.Flat Γ(T, ⊤) (C.X q) := by
    have : Module.Projective Γ(T, ⊤) (C.X q) := hproj q
    infer_instance
  let O := D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))
  let : IsLocalRing O := D.abelian.scheme.left.toLocallyRingedSpace.isLocalRing
    (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))
  let : Algebra Γ(T, ⊤) O := D.poincareAffineStalkAlgebra t hx
  let m := D.poincareAffineParameterIdeal t
  let : m.IsMaximal := D.poincareAffineParameterIdeal_isMaximal_of_zero_mem t hx
  let : IsLocalization m.primeCompl O := D.poincareAffineStalk_isLocalization t hx
  obtain ⟨hvan, ⟨etop⟩⟩ := A.poincareAffine_model_stalk_cohomology_residue
    D hg hN hNk t hx H U hU hUa hUe φ ht
  have hfield := D.poincareAffine_model_field_support t H U hU hUa hUe φ ht
  obtain ⟨hvanC, ⟨etopC⟩⟩ :=
    Single.PointLocalAlgebraCohomology.finiteFlatCochain_cohomology_of_localAlgebra C hfin hf m hfield O g hvan etop
  let E (q : ℕ) : C.homology q ≅
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj L.sheaf) :=
    asIso (HomologicalComplex.homologyMap φ q) ≪≫
      OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso b.appTop.hom L.sheaf U hU hUa q
  constructor
  · intro q hq
    exact (hvanC q hq).of_iso (E q).symm
  · exact ⟨(E g).symm ≪≫ etopC⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

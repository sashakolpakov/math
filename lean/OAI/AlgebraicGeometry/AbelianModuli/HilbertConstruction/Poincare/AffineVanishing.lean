import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineClosedSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.GeometricMinimalModel

/-! # Affine Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual Poincare family has zero cohomology over every Noetherian affine parameter scheme disjoint from the dual zero section. Its finite projective model and finite affine trivializing cover are constructed in the proof. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem Dual.Data.DualAbelianData.poincareAffine_coefficientCohomology_vanish_off_zero
    {S T : Scheme.{u}} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
    (t : T ⟶ D.abelian.scheme.left)
    (hoff : t ⁻¹' Set.range η[D.abelian.scheme].left = ∅) :
    let p := pullback.fst D.abelian.scheme.hom A.scheme.hom;
    let b := pullback.snd p t;
    let L := D.poincare.pullback (pullback.fst p t);
    ∀ q : ℕ, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj L.sheaf) := by
  dsimp only
  let p := pullback.fst D.abelian.scheme.hom A.scheme.hom
  let P := CategoryTheory.Limits.pullback p t
  let a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left := pullback.fst p t
  let b : P ⟶ T := pullback.snd p t
  let H : IsPullback a b p t := IsPullback.of_hasPullback p t
  let L := D.poincare.pullback a
  have hproper : IsProper A.scheme.hom := A.proper
  have hflat : Flat A.scheme.hom := inferInstance
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hproper
  have : Flat p := MorphismProperty.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hflat
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
  have hacyc := D.poincareAffine_model_acyclic_off_zero t H U hU hUa hUe φ ht hfin hf hoff
  intro q
  let E : C.homology q ≅
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj L.sheaf) :=
    asIso (HomologicalComplex.homologyMap φ q) ≪≫
      OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso b.appTop.hom L.sheaf U hU hUa q
  exact (hacyc q).isZero_homology.of_iso E.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

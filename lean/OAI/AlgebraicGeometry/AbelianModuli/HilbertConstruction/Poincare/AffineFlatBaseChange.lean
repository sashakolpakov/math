import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CartesianCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FlatQuotientCohomology

/-! # Affine Flat Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual affine Poincare cohomology formula persists under flat affine
parameter maps, and its top module is the quotient by the extended zero ideal. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareAffine_flatBaseChange_cohomology
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t]
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) t)
    {B : Type u} [CommRing B] (h : Spec (.of B) ⟶ T)
    (hflat : let : Algebra Γ(T, ⊤) B := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap h).toAlgebra; Module.Flat Γ(T, ⊤) B)
    {Q : Scheme.{u}} {a' : Q ⟶ P} {b' : Q ⟶ Spec (.of B)} (H' : IsPullback a' b' b h) :
    (∀ q : ℕ, q ≠ g → IsZero
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b')) q).obj
        (D.poincare.pullback (a' ≫ a)).sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b')) g).obj
      (D.poincare.pullback (a' ≫ a)).sheaf) ≅
        ModuleCat.of B (B ⧸ (D.poincareAffineParameterIdeal t).map (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap h))) := by
  let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom
  have hproper : IsProper A.abelian.scheme.hom := A.abelian.proper
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.abelian.scheme.hom).flip hproper
  have : IsProper b := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace b
  let L := D.poincare.pullback a
  obtain ⟨r, V, ha, he, hcover⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin r) → P.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  obtain ⟨hvan, ⟨etop⟩⟩ := A.poincareAffine_cartesian_cohomology_formula D hg hN hNk t H
  obtain ⟨hvan', ⟨etop'⟩⟩ := HilbertConstruction.Spec.FlatQuotientCohomology.specFlatLineBundle_cohomology_quotient H' L U hU
    (fun i => ha i.down) (fun i => he i.down) hflat g hg
    (D.poincareAffineParameterIdeal t) hvan etop
  let eL : (L.pullback a').sheaf ≅ (D.poincare.pullback (a' ≫ a)).sheaf :=
    (Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf
  let E (q : ℕ) :=
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b')) q).mapIso eL
  exact ⟨fun q hq => (hvan' q hq).of_iso (E q).symm, ⟨(E g).symm ≪≫ etop'⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

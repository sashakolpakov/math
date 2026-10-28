import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.ModelCohomologyBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CochainTruncation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.MinimalRank

/-! # Truncated Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Construct a universal finite free Cech model of the actual dual-zero-stalk Poincare family concentrated in degrees 0 through g. Its minimal first source has rank one and its first coefficients generate the maximal ideal. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareZeroStalk_exists_dimension_bounded_model
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom;
    let b := pullback.snd p D.poincareZeroStalkParameterMap;
    let L := D.poincare.pullback (pullback.fst p D.poincareZeroStalkParameterMap);
    ∃ (k : ℕ) (U : ULift.{u} (Fin k) → (CategoryTheory.Limits.pullback p D.poincareZeroStalkParameterMap).Opens),
      iSup U = ⊤ ∧ (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme)) ∧
      ∃ (C : CochainComplex (ModuleCat.{u} Γ(D.poincareZeroStalkScheme, ⊤)) ℕ)
        (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom L.sheaf U)
        (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)),
        QuasiIso φ ∧ (∀ q, g < q → IsZero (C.X q)) ∧
        (∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q)) ∧
        (∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q)) ∧
        (∀ (B : Type u) [AddCommGroup B] [Module Γ(D.poincareZeroStalkScheme, ⊤) B],
          QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ)) ∧
        Module.finrank Γ(D.poincareZeroStalkScheme, ⊤) Q.complex.X₁ = 1 ∧
        Q.firstDifferentialIdeal = IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) := by
  dsimp only
  let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom
  let t := D.poincareZeroStalkParameterMap
  let P := CategoryTheory.Limits.pullback p t
  let a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left := pullback.fst p t
  let b : P ⟶ D.poincareZeroStalkScheme := pullback.snd p t
  let H : IsPullback a b p t := IsPullback.of_hasPullback p t
  let L := D.poincare.pullback a
  let R := Γ(D.poincareZeroStalkScheme, ⊤)
  have : IsProper A.abelian.scheme.hom := A.abelian.proper
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.abelian.scheme.hom).flip inferInstance
  have : IsProper b := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  obtain ⟨k, U, hU, ha, he, C, φ, _, hφ, hb, hfin, hfree, ht, _, _⟩ :=
    D.poincareZeroStalk_exists_geometric_minimal_model
  have hres := A.poincareZeroStalk_model_residue_cohomology_vanish_above_dimension
    D H U hU ha he φ ht hN hNk
  let T := HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncation C g
  let κ := HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncationι C g
  let ψ := κ ≫ φ
  have hT := HilbertConstruction.Finite.FreeCochainTruncation.finiteCochainTruncation_finite_free C hfin hfree g (hres (g + 1) (Nat.lt_succ_self g))
  have : QuasiIso φ := hφ
  have : QuasiIso κ := HilbertConstruction.Finite.FreeCochainTruncation.finiteCochainTruncation_quasiIso_of_residue_bound C hfin hfree g hres
  have hψ : QuasiIso ψ := quasiIso_comp κ φ
  have ht' : ∀ (B : Type u) [AddCommGroup B] [Module R B], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B ψ) := by
    intro B _ _
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B κ) :=
      Universal.CochainTruncation.finiteCochainTruncation_tensor_quasiIso_of_residue_bound C hb hfin hfree g hres B
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ) := ht B
    change QuasiIso (((HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor B).mapHomologicalComplex (.up ℕ)).map (κ ≫ φ))
    rw [Functor.map_comp]
    infer_instance
  have : Module.Finite R (T.sc' 0 1 2).X₁ := (hT 0).1
  have : Module.Free R (T.sc' 0 1 2).X₁ := (hT 0).2
  have : Module.Finite R (T.sc' 0 1 2).X₂ := (hT 1).1
  have : Module.Free R (T.sc' 0 1 2).X₂ := (hT 1).2
  have : Module.Finite R (T.sc' 0 1 2).X₃ := (hT 2).1
  have : Module.Free R (T.sc' 0 1 2).X₃ := (hT 2).2
  obtain ⟨Q⟩ := Local.MinimalShortComplex.LocalSectionLifting.exists_localMinimalShortComplex (T.sc' 0 1 2)
  have hdim := D.poincareZeroStalk_minimal_firstModule_finrank_one H U hU ha he ψ ht' Q
  have hI := D.poincareZeroStalk_minimal_firstDifferentialIdeal_eq_maximal H U hU ha he ψ ht' Q
  exact ⟨k, U, hU, ha, he, T, ψ, Q, hψ,
    fun q hq => HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncation_isZero_above C g q hq,
    fun q => (hT q).1, fun q => (hT q).2, ht', hdim, hI⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

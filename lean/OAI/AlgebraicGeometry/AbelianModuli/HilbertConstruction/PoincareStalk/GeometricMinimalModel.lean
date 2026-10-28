import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.MinimalSource
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.LocalMinimalCechModel
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Geometric Minimal Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! At the rational zero point of the dual abelian variety, the genuine Poincare family has a constructed universal finite free Cech model and a constructed local minimal short complex whose first differential generates the maximal ideal. No model, support, nonzero source, or coefficient-ideal equality is assumed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)

instance Dual.Data.DualAbelianData.poincareZeroStalkGlobalSections_isNoetherianRing :
    IsNoetherianRing Γ(D.poincareZeroStalkScheme, ⊤) := by
  have : IsLocallyNoetherian D.abelian.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian D.abelian.scheme.hom
  let x := η[D.abelian.scheme].left (IsLocalRing.closedPoint K)
  have : IsNoetherianRing (D.abelian.scheme.left.presheaf.stalk x) :=
    AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
      (X := D.abelian.scheme.left) (x := x)
  exact isNoetherianRing_of_ringEquiv (D.abelian.scheme.left.presheaf.stalk x)
    (Scheme.ΓSpecIso (D.abelian.scheme.left.presheaf.stalk x)).symm.commRingCatIsoToRingEquiv

theorem Dual.Data.DualAbelianData.poincareZeroStalk_exists_geometric_minimal_model :
    let p := pullback.fst D.abelian.scheme.hom A.scheme.hom;
    let b := pullback.snd p D.poincareZeroStalkParameterMap;
    let L := D.poincare.pullback (pullback.fst p D.poincareZeroStalkParameterMap);
    ∃ (k : ℕ) (U : ULift.{u} (Fin k) → (CategoryTheory.Limits.pullback p D.poincareZeroStalkParameterMap).Opens),
      iSup U = ⊤ ∧ (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme)) ∧
      ∃ (C : CochainComplex (ModuleCat.{u} Γ(D.poincareZeroStalkScheme, ⊤)) ℕ)
        (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom L.sheaf U)
        (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)),
        QuasiIso φ ∧
        (∃ N, ∀ q, N ≤ q → IsZero (C.X q)) ∧
        (∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q)) ∧
        (∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q)) ∧
        (∀ (B : Type u) [AddCommGroup B] [Module Γ(D.poincareZeroStalkScheme, ⊤) B],
          QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ)) ∧
        Nontrivial Q.complex.X₁ ∧
        Q.firstDifferentialIdeal = IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) := by
  dsimp only
  let p := pullback.fst D.abelian.scheme.hom A.scheme.hom
  let t := D.poincareZeroStalkParameterMap
  let P := CategoryTheory.Limits.pullback p t
  let a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left := pullback.fst p t
  let b : P ⟶ D.poincareZeroStalkScheme := pullback.snd p t
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
  obtain ⟨C, φ, Q, hφ, hb, hfin, hfree, ht, _, _⟩ :=
    ProperFlat.LocalMinimalCechModel.properFlat_exists_local_minimal_cech_model b L U hU hUa
  have hn : Nontrivial Q.complex.X₁ :=
    D.poincareZeroStalk_minimal_firstModule_nontrivial H U hU hUa hUe φ ht Q
  have hI : Q.firstDifferentialIdeal = IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) :=
    D.poincareZeroStalk_minimal_firstDifferentialIdeal_eq_maximal H U hU hUa hUe φ ht Q
  exact ⟨k, U, hU, hUa, hUe, C, φ, Q, hφ, hb, hfin, hfree, ht, hn, hI⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

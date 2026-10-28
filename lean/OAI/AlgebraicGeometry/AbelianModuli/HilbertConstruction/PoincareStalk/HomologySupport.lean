import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.ResidueCycleSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HomologySupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroCycles

/-! # Homology Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every homology module of a finite free model of the actual dual-zero-stalk Poincare family is supported at the maximal ideal. All residue degrees away from the dual zero are handled by the genuine field-fiber vanishing theorem. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)
variable {P : Scheme.{u}} [P.IsSeparated]
variable {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ D.poincareZeroStalkScheme}
variable (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) D.poincareZeroStalkParameterMap)
variable {κ : Type u} [LinearOrder κ] [Finite κ] (U : κ → P.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
  (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
variable {C : CochainComplex (ModuleCat.{u} Γ(D.poincareZeroStalkScheme, ⊤)) ℕ}
variable (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
variable (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(D.poincareZeroStalkScheme, ⊤) B],
  QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareZeroStalk_residue_model_acyclic_away_closedPoint
    (v : PrimeSpectrum Γ(D.poincareZeroStalkScheme, ⊤))
    (hv : v ≠ IsLocalRing.closedPoint Γ(D.poincareZeroStalkScheme, ⊤)) :
    (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(D.poincareZeroStalkScheme, ⊤)
      v.asIdeal.ResidueField).mapHomologicalComplex (.up ℕ)).obj C).Acyclic := by
  have : IsLocalRing Γ(Spec (D.abelian.scheme.left.presheaf.stalk
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))), ⊤) :=
    Dual.Data.DualAbelianData.poincareZeroStalkGlobalSections_isLocalRing D
  let T := D.poincareZeroStalkScheme
  let t := D.poincareZeroStalkParameterMap
  let R := Γ(T, ⊤)
  let B := v.asIdeal.ResidueField
  let Cκ := ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C
  intro q
  cases q with
  | zero =>
    have hk : Subsingleton (Cκ.d 0 1).hom.ker :=
      D.poincareZeroStalk_firstResidueCycles_vanish H U hU ha he φ ht v hv
    have : Subsingleton (Cκ.d 0 1).hom.ker := hk
    have hz : IsZero (Cκ.cycles 0) :=
      (Cochain.ZeroCycles.CochainZeroCycles.cyclesIso Cκ).isZero_iff.mpr (ModuleCat.isZero_of_subsingleton _)
    exact (Cκ.exactAt_iff_isZero_homology 0).mpr ((CochainComplex.isoHomologyπ₀ Cκ).isZero_iff.mp hz)
  | succ n =>
    let j : Spec (.of B) ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
    let a' := pullback.fst b j
    let b' := pullback.snd b j
    let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
    let c : Spec (.of B) ⟶ Spec (.of K) := (j ≫ t) ≫ D.abelian.scheme.hom
    let x : (Over.map c).obj (𝟙_ (Over (Spec (.of B)))) ⟶ D.abelian.scheme :=
      Over.homMk (j ≫ t) (by change _ = (𝟙 _) ≫ c; exact (Category.id_comp c).symm)
    have hz : η[D.abelian.scheme].left ≫ D.abelian.scheme.hom = 𝟙 (Spec (.of K)) :=
      η[D.abelian.scheme].w
    have hx : x ≠ 1 := by
      intro h
      apply Affine.StalkCoefficientSupport.affine_stalk_primeResidue_ne_rational_zero D.abelian.scheme.hom η[D.abelian.scheme].left hz v hv
      have hh := congrArg Over.Hom.left h
      rw [Hom.one_def] at hh
      change j ≫ t = ((𝟙 _) ≫ c) ≫ η[D.abelian.scheme].left at hh
      exact hh.trans (congrArg (fun w : Spec (.of B) ⟶ Spec (.of K) => w ≫ η[D.abelian.scheme].left)
        (Category.id_comp c))
    let HF : IsPullback (a' ≫ a) b' (pullback.fst D.abelian.scheme.hom A.scheme.hom) x.left :=
      H'.paste_horiz H
    have hzero := D.poincareFieldFiber_cohomology_vanish c x HF hx (n + 1)
    let L := D.poincare.pullback a
    let e : (L.pullback a').sheaf ≅ (D.poincare.pullback (a' ≫ a)).sheaf :=
      (Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf
    let eH := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (CategoryTheory.Limits.pullback b j) (n + 1)).mapIso e
    have hi : Function.Injective eH.hom := (AddCommGrpCat.mono_iff_injective eH.hom).mp inferInstance
    have hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a').sheaf (n + 1)) :=
      ⟨fun y z => hi (hzero.elim _ _)⟩
    have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra = (inferInstance : Algebra R B) := by
      rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
      exact toAlgebra_algebraMap
    have hres := HilbertConstruction.Spec.ModelVanishing.spec_model_exactAt_of_cohomology_zero H' L U hU ha he φ ht n hL
    erw [hAlg] at hres
    exact hres

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareZeroStalk_model_homology_support
    (hfin : ∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (hfree : ∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q)) (q : ℕ) :
    Module.support Γ(D.poincareZeroStalkScheme, ⊤) (C.homology q) ⊆
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) : Set Γ(D.poincareZeroStalkScheme, ⊤)) := by
  apply Cochain.HomologySupport.finiteFreeCochain_homology_support_of_residue_exactAt C hfin hfree _ q
  intro v hv
  have hne : v ≠ IsLocalRing.closedPoint Γ(D.poincareZeroStalkScheme, ⊤) := by
    intro h
    apply hv
    subst v
    exact le_rfl
  exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor C q).mp
    (D.poincareZeroStalk_residue_model_acyclic_away_closedPoint H U hU ha he φ ht v hne q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

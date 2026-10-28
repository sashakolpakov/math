import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FieldCohomologyBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.CochainVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.GeometricMinimalModel

/-! # Model Cohomology Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual dual-zero-stalk Poincare model has residue cohomology only through degree g. For a finite free model this bound survives every additive functor, and its degree-g cycles are a split finite free submodule. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
variable {P : Scheme.{u}} [P.IsSeparated]
variable {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left} {b : P ⟶ D.poincareZeroStalkScheme}
variable (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom)
  D.poincareZeroStalkParameterMap)
variable {κ : Type u} [LinearOrder κ] [Finite κ] (U : κ → P.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
  (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
variable {C : CochainComplex (ModuleCat.{u} Γ(D.poincareZeroStalkScheme, ⊤)) ℕ}
variable (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
variable (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(D.poincareZeroStalkScheme, ⊤) B],
  QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))

include H hU ha he ht in
theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareZeroStalk_model_residue_cohomology_vanish_above_dimension
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (q : ℕ) (hq : g < q) :
    IsZero ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(D.poincareZeroStalkScheme, ⊤)
      (IsLocalRing.ResidueField Γ(D.poincareZeroStalkScheme, ⊤))).mapHomologicalComplex (.up ℕ)).obj C).homology q) := by
  cases q with
  | zero => exact (Nat.not_lt_zero g hq).elim
  | succ n =>
    let T := D.poincareZeroStalkScheme
    let t := D.poincareZeroStalkParameterMap
    let R := Γ(T, ⊤)
    let B := IsLocalRing.ResidueField R
    let j : Spec (.of B) ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
    let a' := pullback.fst b j
    let b' := pullback.snd b j
    let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
    let c : Spec (.of B) ⟶ Spec (.of K) := (j ≫ t) ≫ D.abelian.scheme.hom
    let x : (Over.map c).obj (𝟙_ (Over (Spec (.of B)))) ⟶ D.abelian.scheme :=
      Over.homMk (j ≫ t) (by change _ = (𝟙 _) ≫ c; exact (Category.id_comp c).symm)
    let HF : IsPullback (a' ≫ a) b' (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) x.left :=
      H'.paste_horiz H
    let κ : K →+* B := (Scheme.ΓSpecIso (.of B)).hom.hom.comp (Coefficient.ModulePresheaf.schemeCoefficientMap c)
    have hNB : (N : B) ≠ 0 := by
      intro hz
      apply hNk
      apply κ.injective
      simpa only [map_natCast, map_zero] using hz
    have hzero := A.poincareFieldFiber_cohomology_vanish_above_dimension D c x HF hN hNB (n + 1) hq
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
    have hexa : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex
        (.up ℕ)).obj C).ExactAt (n + 1) := by
      erw [hAlg] at hres
      exact hres
    exact hexa.isZero_homology

include H hU ha he ht in
theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareZeroStalk_model_map_cohomology_vanish_above_dimension
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (hfin : ∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (hfree : ∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    {E : Type v} [Category.{w} E] [Abelian E]
    (F : ModuleCat.{u} Γ(D.poincareZeroStalkScheme, ⊤) ⥤ E) [F.Additive] :
    ∀ q, g < q → IsZero (((F.mapHomologicalComplex (.up ℕ)).obj C).homology q) :=
  Residue.CochainVanishing.LocalSectionLifting.finiteFreeCochain_map_vanish_above_residue_bound F C hfin hfree g
    (A.poincareZeroStalk_model_residue_cohomology_vanish_above_dimension D H U hU ha he φ ht hN hNk)

include H hU ha he ht in
theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareZeroStalk_model_last_cycles_finite_free
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (hfin : ∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (hfree : ∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q)) :
    Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.d g (g + 1)).hom.ker ∧
      Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.d g (g + 1)).hom.ker := by
  have hres := A.poincareZeroStalk_model_residue_cohomology_vanish_above_dimension
    D H U hU ha he φ ht hN hNk (g + 1) (Nat.lt_succ_self g)
  obtain ⟨hf, hfr, _⟩ :=
    Residue.CochainVanishing.LocalSectionLifting.finiteFreeCochain_last_cycles_split_finite_free C hfin hfree g hres
  exact ⟨hf, hfr⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

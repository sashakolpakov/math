import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.MinimalIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkCoefficientSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModelFirstCycles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FieldFiberCohomology

/-! # Residue Cycle Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The genuine universal Cech model of the Poincare family on the stalk at the rational dual zero point has first residue cycles supported at the maximal ideal. Nonidentity of each other prime's actual field point follows from its coefficient kernel; vanishing follows from the actual Poincare field-fiber theorem. -/
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
theorem Dual.Data.DualAbelianData.poincareZeroStalk_firstResidueCycles_vanish
    (v : PrimeSpectrum Γ(D.poincareZeroStalkScheme, ⊤))
    (hv : v ≠ IsLocalRing.closedPoint Γ(D.poincareZeroStalkScheme, ⊤)) :
    Subsingleton (LinearMap.ker
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex Γ(D.poincareZeroStalkScheme, ⊤)
        v.asIdeal.ResidueField (C.sc' 0 1 2)).f.hom) := by
  have : IsLocalRing Γ(Spec (D.abelian.scheme.left.presheaf.stalk
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))), ⊤) :=
    Dual.Data.DualAbelianData.poincareZeroStalkGlobalSections_isLocalRing D
  let T := D.poincareZeroStalkScheme
  let t := D.poincareZeroStalkParameterMap
  let R := Γ(T, ⊤)
  let B := v.asIdeal.ResidueField
  let j : Spec (.of B) ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
  let c : Spec (.of B) ⟶ Spec (.of K) := (j ≫ t) ≫ D.abelian.scheme.hom
  let x : (Over.map c).obj (𝟙_ (Over (Spec (.of B)))) ⟶ D.abelian.scheme :=
    Over.homMk (j ≫ t) (by change _ = (𝟙 _) ≫ c; exact (Category.id_comp c).symm)
  have hz : η[D.abelian.scheme].left ≫ D.abelian.scheme.hom = 𝟙 (Spec (.of K)) := η[D.abelian.scheme].w
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
  have hzero := D.poincareFieldFiber_cohomology_vanish c x HF hx 0
  let L := D.poincare.pullback a
  let e : (L.pullback a').sheaf ≅ (D.poincare.pullback (a' ≫ a)).sheaf :=
    (Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf
  let eH := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (CategoryTheory.Limits.pullback b j) 0).mapIso e
  have hi : Function.Injective eH.hom := (AddCommGrpCat.mono_iff_injective eH.hom).mp inferInstance
  have hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a').sheaf 0) :=
    ⟨fun y z => hi (hzero.elim _ _)⟩
  have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra = (inferInstance : Algebra R B) := by
    rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
    exact toAlgebra_algebraMap
  have hres :
      letI : Algebra R B := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra
      Subsingleton (LinearMap.ker
        (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B (C.sc' 0 1 2)).f.hom) := by
    let : Algebra R B := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra
    let : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
    let : Module R B := (inferInstance : Algebra R B).toModule
    let q : B →+* Γ(CategoryTheory.Limits.pullback b j, ⊤) := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b')
    have hq : q.comp (algebraMap R B) = a'.appTop.hom.comp b.appTop.hom :=
      HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficient_compatible H'
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra j) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra j)
    have hcomparison := HilbertConstruction.Spec.CoefficientCechComparison.spec_affineFrame_coefficientCechModel_quasiIsoAt H' U L ha he φ 0
    exact Coefficient.ModelFirstCycles.coefficientCechModel_firstCycles_subsingleton_of_cohomology_zero (hψ := hcomparison)
      a' b.appTop.hom L.sheaf q hq U hU φ hL
  erw [hAlg] at hres
  exact hres

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareZeroStalk_firstDifferentialIdeal_eq_maximal_of_nontrivial_minimal_source
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) [Nontrivial Q.complex.X₁] :
    Q.firstDifferentialIdeal = IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) :=
  D.poincareZeroStalk_firstDifferentialIdeal_eq_maximal_of_residue_support H U hU ha he φ ht Q
    (IsLocalRing.closedPoint Γ(D.poincareZeroStalkScheme, ⊤))
    (fun v hv => D.poincareZeroStalk_firstResidueCycles_vanish H U hU ha he φ ht v hv)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.HomologySupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelAllDegreeVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FieldSupport

/-! # Field Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The genuine Poincare stalk model is acyclic after every field-valued coefficient map whose kernel does not contain the maximal ideal. This stronger support condition survives scalar quotients. -/
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
theorem Dual.Data.DualAbelianData.poincareZeroStalk_model_field_support :
    Cochain.FieldSupport.CochainFieldSupport C (IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤)) := by
  intro B _ _ hnot
  have : IsLocalRing Γ(Spec (D.abelian.scheme.left.presheaf.stalk
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))), ⊤) :=
    Dual.Data.DualAbelianData.poincareZeroStalkGlobalSections_isLocalRing D
  let T := D.poincareZeroStalkScheme
  let t := D.poincareZeroStalkParameterMap
  let R := Γ(T, ⊤)
  let j : Spec (.of B) ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
  let c : Spec (.of B) ⟶ Spec (.of K) := (j ≫ t) ≫ D.abelian.scheme.hom
  let x : (Over.map c).obj (𝟙_ (Over (Spec (.of B)))) ⟶ D.abelian.scheme :=
    Over.homMk (j ≫ t) (by change _ = (𝟙 _) ≫ c; exact (Category.id_comp c).symm)
  have hx : x ≠ 1 := by
    intro h
    apply hnot
    apply Affine.StalkCoefficientSupport.affine_stalk_coefficient_maximal_le_kernel_of_rational_zero
      D.abelian.scheme.hom η[D.abelian.scheme].left η[D.abelian.scheme].w (algebraMap R B)
    have hh := congrArg Over.Hom.left h
    rw [Hom.one_def] at hh
    change j ≫ t = ((𝟙 _) ≫ c) ≫ η[D.abelian.scheme].left at hh
    exact hh.trans (congrArg (fun w : Spec (.of B) ⟶ Spec (.of K) => w ≫ η[D.abelian.scheme].left)
      (Category.id_comp c))
  let HF : IsPullback (a' ≫ a) b' (pullback.fst D.abelian.scheme.hom A.scheme.hom) x.left :=
    H'.paste_horiz H
  let L := D.poincare.pullback a
  let e : (L.pullback a').sheaf ≅ (D.poincare.pullback (a' ≫ a)).sheaf :=
    (Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf
  have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra = (inferInstance : Algebra R B) := by
    rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
    exact toAlgebra_algebraMap
  intro q
  have hzero := D.poincareFieldFiber_cohomology_vanish c x HF hx q
  let eH := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (CategoryTheory.Limits.pullback b j) q).mapIso e
  have hi : Function.Injective eH.hom := (AddCommGrpCat.mono_iff_injective eH.hom).mp inferInstance
  have hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a').sheaf q) :=
    ⟨fun y z => hi (hzero.elim _ _)⟩
  have hres := HilbertConstruction.Spec.ModelAllDegreeVanishing.spec_model_exactAt_of_cohomology_zero_all H' L U hU ha he φ ht q hL
  have hexa : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).ExactAt q := by
    erw [hAlg] at hres
    exact hres
  exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor C q).mp hexa

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

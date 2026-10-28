import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.ResidueCycleSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointSectionNontrivial

/-! # Minimal Source -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The zero residue fiber of the genuine Poincare family is trivial and has a field-valued point. Hence its global sections, the first residue cycles of its universal Cech model, and the first module of every local minimal model are nonzero. Together with the proved residue support this identifies the coefficient ideal with the maximal ideal. -/
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
theorem Dual.Data.DualAbelianData.poincareZeroStalk_minimal_firstModule_nontrivial
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) : Nontrivial Q.complex.X₁ := by
  have : IsLocalRing Γ(Spec (D.abelian.scheme.left.presheaf.stalk
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))), ⊤) :=
    Dual.Data.DualAbelianData.poincareZeroStalkGlobalSections_isLocalRing D
  let T := D.poincareZeroStalkScheme
  let t := D.poincareZeroStalkParameterMap
  let R := Γ(T, ⊤)
  let B := IsLocalRing.ResidueField R
  let : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
  let : Module R B := (inferInstance : Algebra R B).toModule
  let j : Spec (.of B) ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
  have hjSurj : Function.Surjective (algebraMap R B) := by
    exact IsLocalRing.residue_surjective
  have : IsClosedImmersion j := Affine.QuotientCoefficientMap.affineCoordinateMap_isClosedImmersion (algebraMap R B) hjSurj
  let x₀ := η[D.abelian.scheme].left (IsLocalRing.closedPoint K)
  have : IsLocalRing (D.abelian.scheme.left.presheaf.stalk x₀) := inferInstance
  have hj : j (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint (D.abelian.scheme.left.presheaf.stalk x₀) :=
    QuotientResiduePointZero.closedImmersion_singlePoint_localSpec_image (R := D.abelian.scheme.left.presheaf.stalk x₀) j (IsLocalRing.closedPoint B)
  have hpoint : (j ≫ t) (IsLocalRing.closedPoint B) = x₀ :=
    (congrArg (D.abelian.scheme.left.fromSpecStalk x₀) hj).trans Scheme.fromSpecStalk_closedPoint
  have hz : η[D.abelian.scheme].left ≫ D.abelian.scheme.hom = 𝟙 (Spec (.of K)) := η[D.abelian.scheme].w
  have hzero : j ≫ t = ((j ≫ t) ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left :=
    HilbertConstruction.Field.PointRationalZero.fieldPoint_eq_rational_section_of_point D.abelian.scheme.hom η[D.abelian.scheme].left hz (j ≫ t) hpoint
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
  let HF : IsPullback (a' ≫ a) b' (pullback.fst D.abelian.scheme.hom A.scheme.hom) (j ≫ t) :=
    H'.paste_horiz H
  obtain ⟨ef⟩ := D.poincareBaseFamily_zero_implies_trivial (j ≫ t) HF hzero
  let L := D.poincare.pullback a
  let e : (L.pullback a').sheaf ≅ Line.Bundles.structureModule (CategoryTheory.Limits.pullback b j) :=
    (Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf ≪≫ ef
  let c := (j ≫ t) ≫ D.abelian.scheme.hom
  let v : Spec (.of B) ⟶ A.scheme.left := c ≫ η[A.scheme].left
  have hv : (j ≫ t) ≫ D.abelian.scheme.hom = v ≫ A.scheme.hom := by
    change c = (c ≫ η[A.scheme].left) ≫ A.scheme.hom
    exact ((Category.assoc c η[A.scheme].left A.scheme.hom).trans
      ((congrArg (fun w => c ≫ w) η[A.scheme].w).trans (Category.comp_id c))).symm
  let σ : Spec (.of B) ⟶ (D.abelian.scheme ⊗ A.scheme).left := pullback.lift (j ≫ t) v hv
  have hσ : σ ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom = (𝟙 _) ≫ (j ≫ t) :=
    (pullback.lift_fst (j ≫ t) v hv).trans (Category.id_comp (j ≫ t)).symm
  let y : Spec (.of B) ⟶ CategoryTheory.Limits.pullback b j := HF.lift σ (𝟙 _) hσ
  have : Nontrivial Γ((Scheme.Modules.pullback a').obj L.sheaf, ⊤) :=
    HilbertConstruction.Field.PointSectionNontrivial.trivialModule_globalSections_nontrivial_of_fieldPoint y (L.pullback a').sheaf e
  have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra = (inferInstance : Algebra R B) := by
    rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
    exact toAlgebra_algebraMap
  let q : B →+* Γ(CategoryTheory.Limits.pullback b j, ⊤) := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b')
  have hq : q.comp (algebraMap R B) = a'.appTop.hom.comp b.appTop.hom := by
    have hh := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficient_compatible H'
    erw [hAlg] at hh
    exact hh
  have hψ : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
      Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a' b.appTop.hom L.sheaf q hq U) 0 := by
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra j) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra j)
    have hcomparison :
        letI : Algebra R B := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra
        letI : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
        letI : Module R B := (inferInstance : Algebra R B).toModule
        ∀ hh : q.comp (algebraMap R B) = a'.appTop.hom.comp b.appTop.hom,
          QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
            Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a' b.appTop.hom L.sheaf q hh U) 0 := by
      let : Algebra R B := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra
      let : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
      let : Module R B := (inferInstance : Algebra R B).toModule
      intro hh
      exact HilbertConstruction.Spec.CoefficientCechComparison.spec_affineFrame_coefficientCechModel_quasiIsoAt H' U L ha he φ 0
    erw [hAlg] at hcomparison
    exact hcomparison hq
  exact Coefficient.ModelFirstCycles.minimal_firstModule_nontrivial_of_residue_sections
    a' b.appTop.hom L.sheaf q hq U hU φ Q

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareZeroStalk_minimal_firstDifferentialIdeal_eq_maximal
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) :
    Q.firstDifferentialIdeal = IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) := by
  have : Nontrivial Q.complex.X₁ := D.poincareZeroStalk_minimal_firstModule_nontrivial H U hU ha he φ ht Q
  exact D.poincareZeroStalk_firstDifferentialIdeal_eq_maximal_of_nontrivial_minimal_source H U hU ha he φ ht Q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

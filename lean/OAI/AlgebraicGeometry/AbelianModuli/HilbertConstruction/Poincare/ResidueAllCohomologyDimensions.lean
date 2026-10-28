import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.ResidueAllDimensions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelCohomologyLinearity

/-! # Residue All Cohomology Dimensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual closed residue fiber of the Poincare stalk family has structure-sheaf cohomology of dimension choose(g,q) in every degree q. -/
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
theorem Dual.Data.DualAbelianData.poincareZeroStalk_residue_structure_cohomology_finrank
    (hfin : ∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (hfree : ∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) (q : ℕ) :
    let R := Γ(D.poincareZeroStalkScheme, ⊤);
    let B := IsLocalRing.ResidueField R;
    let j : Spec (.of B) ⟶ D.poincareZeroStalkScheme := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B);
    Module.finrank B
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := pullback.snd b j)) q).obj (Line.Bundles.structureModule (CategoryTheory.Limits.pullback b j))) =
      g.choose q := by
  let R := Γ(D.poincareZeroStalkScheme, ⊤)
  let B := IsLocalRing.ResidueField R
  let j : Spec (.of B) ⟶ D.poincareZeroStalkScheme := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
  let L := D.poincare.pullback a
  let c := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b')
  let CB := ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C
  have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra = (inferInstance : Algebra R B) := by
    rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
    exact toAlgebra_algebraMap
  have hs : Function.Surjective (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j) := by
    rw [Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]
    change Function.Surjective (algebraMap R (IsLocalRing.ResidueField R))
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  let e : CB.homology q ≃ₗ[B]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj (L.pullback a').sheaf) := by
    have hh := HilbertConstruction.Spec.ModelCohomologyLinearity.specModelCohomologyLinearEquiv H' L U hU ha he φ ht hs q
    erw [hAlg] at hh
    exact hh
  have hkill : IsLocalRing.maximalIdeal R ≤ RingHom.ker (algebraMap R B) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have hmodel : Module.finrank B (CB.homology q) = g.choose q :=
    D.poincareZeroStalk_model_closedField_cohomology_finrank
      H U hU ha he φ ht hfin hfree hbound Q B hkill q
  obtain ⟨et⟩ := D.poincareZeroStalk_residue_family_trivial H
  let eT := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).mapIso et
  exact eT.toLinearEquiv.finrank_eq.symm.trans (e.finrank_eq.symm.trans hmodel)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

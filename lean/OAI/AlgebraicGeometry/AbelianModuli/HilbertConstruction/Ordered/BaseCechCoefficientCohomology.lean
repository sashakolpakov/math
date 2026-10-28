import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor

/-! # Base Cech Coefficient Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.BaseCechCoefficientCohomology

noncomputable section

/-! The original base-linear Cech cohomology and the genuine coefficient
cohomology use the same Ext group and the same global scalar action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem originalGlobalSmul_eq_globalModuleScalar
    {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤)) :
    SheafCohomology.AffineH.Projective.globalSmulHom M r = Global.ModuleScalars.globalModuleScalar M r := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  rfl

def baseCohomologyCoefficientLinearEquiv
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (n : ℕ) :
    letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π M n
    SheafCohomology.AffineH.Projective.H M n ≃ₗ[Γ(S, ⊤)]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor π.appTop.hom n).obj M) := by
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π M n
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r x
  change (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X n).map
      (SheafCohomology.AffineH.Projective.globalSmulHom M (π.appTop r)) x =
    (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X n).map (Global.ModuleScalars.globalModuleScalar M (π.appTop r)) x
  rw [originalGlobalSmul_eq_globalModuleScalar]

def orderedBaseCechCoefficientCohomologyLinearEquiv
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent]
    {I : Type u} [LinearOrder I] (U : I → X.Opens) (hU : IsOpenCover U)
    (ha : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology n ≃ₗ[Γ(S, ⊤)]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor π.appTop.hom n).obj M) := by
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π M n
  exact (SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv
    π M U hU ha n).trans (baseCohomologyCoefficientLinearEquiv π M n)

def orderedBaseCechH1CoefficientLinearEquiv
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent]
    {I : Type u} [LinearOrder I] (U : I → X.Opens) (hU : IsOpenCover U)
    (ha : ∀ i, IsAffineOpen (U i)) :
    ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2).homology ≃ₗ[Γ(S, ⊤)]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor π.appTop.hom 1).obj M) :=
  ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homologyIsoSc' 0 1 2 (by simp) (by simp)).symm.toLinearEquiv.trans
    (orderedBaseCechCoefficientCohomologyLinearEquiv π M U hU ha 1)

theorem orderedBaseCech_H1_finrank_coefficient
    {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent]
    {I : Type u} [LinearOrder I] (U : I → X.Opens) (hU : IsOpenCover U)
    (ha : ∀ i, IsAffineOpen (U i)) :
    Module.finrank Γ(S, ⊤) ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2).homology =
      Module.finrank Γ(S, ⊤)
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor π.appTop.hom 1).obj M) :=
  (orderedBaseCechH1CoefficientLinearEquiv π M U hU ha).finrank_eq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.BaseCechCoefficientCohomology

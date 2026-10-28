import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelResidueDimensions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.DualResolution

/-! # Residue All Dimensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! All cohomology dimensions of a residue-field specialization of the actual Poincare stalk model are the binomial coefficients of the geometric dimension. -/
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
variable (hfin : ∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
variable (hfree : ∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
variable (hbound : ∀ q, g < q → IsZero (C.X q))
variable (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))

include H hU ha he ht hfin hfree hbound Q in
theorem Dual.Data.DualAbelianData.poincareZeroStalk_model_closedField_cohomology_finrank
    (B : Type u) [Field B] [Algebra Γ(D.poincareZeroStalkScheme, ⊤) B]
    (hkill : IsLocalRing.maximalIdeal Γ(D.poincareZeroStalkScheme, ⊤) ≤
      RingHom.ker (algebraMap Γ(D.poincareZeroStalkScheme, ⊤) B)) (q : ℕ) :
    Module.finrank B
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(D.poincareZeroStalkScheme, ⊤) B).mapHomologicalComplex
        (.up ℕ)).obj C).homology q) = g.choose q := by
  let R := Γ(D.poincareZeroStalkScheme, ⊤)
  let rs := Classical.choose D.poincareZeroStalk_regular_parameters
  have hrs := Classical.choose_spec D.poincareZeroStalk_regular_parameters
  let e : R ≃ₗ[R] Q.complex.X₁ := Classical.choice
    (Module.nonempty_linearEquiv_of_finrank_eq_one
      (D.poincareZeroStalk_minimal_firstModule_finrank_one H U hU ha he φ ht Q))
  have hI := D.poincareZeroStalk_minimal_firstDifferentialIdeal_eq_maximal H U hU ha he φ ht Q
  exact Minimal.ModelResidueDimensions.minimalModel_closedField_cohomology_finrank C g hfin hfree hbound rs hrs.2.2 hrs.1 hrs.2.1
    (D.poincareZeroStalk_model_field_support H U hU ha he φ ht) Q e hI B hkill q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

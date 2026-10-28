import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.FieldSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.RegularParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalCochainAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.ModelCohomologyBound

/-! # Top Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual finite free Poincare stalk model has no cohomology below g. For polarized full-level data, the upper bound implies that its cohomology over the local coefficient ring is concentrated in degree g. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
section
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
theorem Dual.Data.DualAbelianData.poincareZeroStalk_model_cohomology_vanish_below_dimension
    (hfin : ∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (hfree : ∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (q : ℕ) (hq : q < g) : IsZero (C.homology q) := by
  obtain ⟨rs, hreg, hgen, hlen⟩ := D.poincareZeroStalk_regular_parameters
  exact Regular.LocalCochainAcyclicity.regularLocalCochain_homology_zero_below_regular_parameters g Γ(D.poincareZeroStalkScheme, ⊤)
    C hfin hfree rs hlen hreg hgen
    (D.poincareZeroStalk_model_field_support H U hU ha he φ ht) q hq

end

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareZeroStalk_model_cohomology_concentrated_in_dimension
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    {P : Scheme.{u}} [P.IsSeparated]
    {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left} {b : P ⟶ D.poincareZeroStalkScheme}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) D.poincareZeroStalkParameterMap)
    {κ : Type u} [LinearOrder κ] [Finite κ] (U : κ → P.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
      (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    {C : CochainComplex (ModuleCat.{u} Γ(D.poincareZeroStalkScheme, ⊤)) ℕ}
    (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
    (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(D.poincareZeroStalkScheme, ⊤) B],
      QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))
    (hfin : ∀ q, Module.Finite Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (hfree : ∀ q, Module.Free Γ(D.poincareZeroStalkScheme, ⊤) (C.X q))
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (q : ℕ) (hq : q ≠ g) : IsZero (C.homology q) := by
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · exact D.poincareZeroStalk_model_cohomology_vanish_below_dimension H U hU ha he φ ht hfin hfree q hlt
  · exact A.poincareZeroStalk_model_map_cohomology_vanish_above_dimension
      D H U hU ha he φ ht hN hNk hfin hfree (𝟭 _) q hgt

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

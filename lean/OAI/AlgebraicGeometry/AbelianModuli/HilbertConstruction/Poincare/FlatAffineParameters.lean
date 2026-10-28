import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineFlatBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterCoordinateComparison

/-! # Flat Affine Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Poincare quotient formula on flat affine parameter schemes is stated
using their actual global coordinate rings and actual Cartesian families. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincare_flatAffineParameter_cohomology
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t]
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) t)
    {Y : Scheme.{u}} [IsAffine Y] (s : Y ⟶ T) [Flat s]
    {Q : Scheme.{u}} {a' : Q ⟶ P} {b' : Q ⟶ Y} (H' : IsPullback a' b' b s) :
    (∀ q : ℕ, q ≠ g → IsZero
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b'.appTop.hom q).obj
        (D.poincare.pullback (a' ≫ a)).sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b'.appTop.hom g).obj
      (D.poincare.pullback (a' ≫ a)).sheaf) ≅
        ModuleCat.of Γ(Y, ⊤) (Γ(Y, ⊤) ⧸ (D.poincareAffineParameterIdeal t).map s.appTop.hom)) := by
  have hflat : let : Algebra Γ(T, ⊤) Γ(Y, ⊤) :=
      (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap (Y.isoSpec.inv ≫ s)).toAlgebra;
      Module.Flat Γ(T, ⊤) Γ(Y, ⊤) := by
    rw [Affine.ParameterCoordinateComparison.specBaseCoefficientMap_isoSpec_inv_comp]
    exact s.flat_appTop
  have h := A.poincareAffine_flatBaseChange_cohomology D hg hN hNk t H
    (Y.isoSpec.inv ≫ s) hflat (Affine.ParameterCoordinateComparison.affineParameter_isPullback_spec H')
  simp only [Affine.ParameterCoordinateComparison.specPullbackCoefficientMap_comp_isoSpec_hom] at h
  erw [Affine.ParameterCoordinateComparison.specBaseCoefficientMap_isoSpec_inv_comp s] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

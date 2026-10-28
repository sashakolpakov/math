import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineZeroPoint

/-! # Zero Affine Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An affine open containing the dual zero has a constructed lift of the zero section. Its Poincare support ideal is maximal and its coordinate quotient is the original ground field. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) {T : Scheme.{u}} [IsAffine T]
variable (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t]
variable (hx : η[D.abelian.scheme].left (IsLocalRing.closedPoint K) ∈ Set.range t)

include hx in
omit [IsAffine T] in
theorem Dual.Data.DualAbelianData.poincareAffine_exists_zero_lift : ∃ z : Spec (.of K) ⟶ T, z ≫ t = η[D.abelian.scheme].left := by
  have hRange : Set.range η[D.abelian.scheme].left ⊆ Set.range t := by
    rintro y ⟨v, rfl⟩
    have hv : v = IsLocalRing.closedPoint K :=
      @Subsingleton.elim (PrimeSpectrum K) inferInstance _ _
    simpa only [hv] using hx
  exact ⟨IsOpenImmersion.lift t η[D.abelian.scheme].left hRange,
    IsOpenImmersion.lift_fac t η[D.abelian.scheme].left hRange⟩

def Dual.Data.DualAbelianData.poincareAffineZeroLift : Spec (.of K) ⟶ T :=
  Classical.choose (D.poincareAffine_exists_zero_lift t hx)

omit [IsAffine T] in
theorem Dual.Data.DualAbelianData.poincareAffineZeroLift_fac :
    D.poincareAffineZeroLift t hx ≫ t = η[D.abelian.scheme].left :=
  Classical.choose_spec (D.poincareAffine_exists_zero_lift t hx)

omit [IsAffine T] in
theorem Dual.Data.DualAbelianData.poincareAffineZeroLift_section :
    D.poincareAffineZeroLift t hx ≫ (t ≫ D.abelian.scheme.hom) = 𝟙 _ :=
  D.poincareAffine_liftedZero_section t (D.poincareAffineZeroLift t hx) (D.poincareAffineZeroLift_fac t hx)

include hx in
theorem Dual.Data.DualAbelianData.poincareAffineParameterIdeal_isMaximal_of_zero_mem :
    (D.poincareAffineParameterIdeal t).IsMaximal :=
  D.poincareAffineParameterIdeal_isMaximal t (D.poincareAffineZeroLift t hx) (D.poincareAffineZeroLift_fac t hx)

def Dual.Data.DualAbelianData.poincareAffineParameterQuotientEquiv : (Γ(T, ⊤) ⧸ D.poincareAffineParameterIdeal t) ≃+* K := by
  let z := D.poincareAffineZeroLift t hx
  have hz := D.poincareAffineZeroLift_fac t hx
  rw [D.poincareAffineParameterIdeal_eq_rationalPointIdeal t z hz]
  exact Affine.RationalPointIdeal.affineRationalPointQuotientEquiv (t ≫ D.abelian.scheme.hom) z (D.poincareAffineZeroLift_section t hx)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

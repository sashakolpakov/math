import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineClosedSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RationalPointIdeal

/-! # Affine Zero Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On an affine open neighborhood of the dual zero over a field, the geometric Poincare support ideal is exactly the maximal ideal of the lifted rational zero point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) {T : Scheme.{u}} [IsAffine T]
variable (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t]
variable (z : Spec (.of K) ⟶ T) (hz : z ≫ t = η[D.abelian.scheme].left)

include hz in
omit [IsAffine T] [IsOpenImmersion t] in
theorem Dual.Data.DualAbelianData.poincareAffine_liftedZero_section :
    z ≫ (t ≫ D.abelian.scheme.hom) = 𝟙 _ :=
  (Category.assoc z t D.abelian.scheme.hom).symm.trans
    ((congrArg (fun f => f ≫ D.abelian.scheme.hom) hz).trans η[D.abelian.scheme].w)

include hz in
omit [IsAffine T] in
theorem Dual.Data.DualAbelianData.poincareAffine_zero_preimage_singleton :
    t ⁻¹' Set.range η[D.abelian.scheme].left = {z (IsLocalRing.closedPoint K)} := by
  have ht := congrArg (fun f : Spec (.of K) ⟶ D.abelian.scheme.left =>
    f (IsLocalRing.closedPoint K)) hz
  ext y
  constructor
  · rintro ⟨v, hv⟩
    apply Set.mem_singleton_iff.mpr
    apply t.isOpenEmbedding.injective
    exact hv.symm.trans ((congrArg η[D.abelian.scheme].left
      (Subsingleton.elim (show Spec (.of K) from v) (IsLocalRing.closedPoint K))).trans ht.symm)
  · intro hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact ⟨IsLocalRing.closedPoint K, ht.symm⟩

include hz in
theorem Dual.Data.DualAbelianData.poincareAffineParameterIdeal_eq_rationalPointIdeal :
    D.poincareAffineParameterIdeal t = Affine.RationalPointIdeal.affineRationalPointIdeal z := by
  change PrimeSpectrum.vanishingIdeal
    (T.isoSpec.hom '' (t ⁻¹' Set.range η[D.abelian.scheme].left)) =
      (T.isoSpec.hom (z (IsLocalRing.closedPoint K))).asIdeal
  rw [D.poincareAffine_zero_preimage_singleton t z hz, Set.image_singleton,
    PrimeSpectrum.vanishingIdeal_singleton]

include hz in
theorem Dual.Data.DualAbelianData.poincareAffineParameterIdeal_isMaximal : (D.poincareAffineParameterIdeal t).IsMaximal := by
  rw [D.poincareAffineParameterIdeal_eq_rationalPointIdeal t z hz]
  exact Affine.RationalPointIdeal.affineRationalPointIdeal_isMaximal (t ≫ D.abelian.scheme.hom) z
    (D.poincareAffine_liftedZero_section t z hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

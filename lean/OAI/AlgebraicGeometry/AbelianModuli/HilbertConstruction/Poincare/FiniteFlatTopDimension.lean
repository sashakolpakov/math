import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FiniteFlatGlobalCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RationalFiberQuotient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FieldCoordinateRank

/-! # Finite Flat Top Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The top cohomology of Poincare pulled back by a finite flat parameter
map has dimension the degree of that map at the dual zero point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincare_finiteFlat_top_finrank
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {T : Scheme.{u}} [T.IsSeparated] [IsLocallyNoetherian T]
    (t : T ⟶ D.abelian.scheme.left) [IsFinite t] [Flat t]
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) t) :
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b ≫ (t ≫ D.abelian.scheme.hom))) g).obj
        (D.poincare.pullback a).sheaf) =
      t.finrank (η[D.abelian.scheme].left (IsLocalRing.closedPoint K)) := by
  let z := η[D.abelian.scheme].left (IsLocalRing.closedPoint K)
  obtain ⟨U, hUa, hz, _⟩ := exists_isAffineOpen_mem_and_subset
    (show z ∈ (⊤ : D.abelian.scheme.left.Opens) from trivial)
  have : IsAffine U.toScheme := hUa
  have hU : Set.range η[D.abelian.scheme].left ⊆ U := by
    rintro y ⟨x, rfl⟩
    have he : η[D.abelian.scheme].left x = z :=
      congrArg η[D.abelian.scheme].left
        (@Subsingleton.elim (PrimeSpectrum K) inferInstance x (IsLocalRing.closedPoint K))
    exact he.symm ▸ hz
  have hx : z ∈ Set.range U.ι := ⟨⟨z, hz⟩, rfl⟩
  let Y := t ⁻¹ᵁ U
  let s := t ∣_ U
  have : IsAffine Y.toScheme := hUa.preimage t
  let zU := D.poincareAffineZeroLift U.ι hx
  let pU := U.ι ≫ D.abelian.scheme.hom
  have hzU : zU ≫ pU = 𝟙 _ := D.poincareAffineZeroLift_section U.ι hx
  have hzfac : zU ≫ U.ι = η[D.abelian.scheme].left := D.poincareAffineZeroLift_fac U.ι hx
  let Z := CategoryTheory.Limits.pullback t η[D.abelian.scheme].left
  let j : Z ⟶ T := pullback.fst t η[D.abelian.scheme].left
  let bZ : Z ⟶ Spec (.of K) := pullback.snd t η[D.abelian.scheme].left
  have HZ : IsPullback j bZ t η[D.abelian.scheme].left := IsPullback.of_hasPullback t η[D.abelian.scheme].left
  have HW : IsPullback j bZ t (zU ≫ U.ι) := by rw [hzfac]; exact HZ
  let α := Cartesian.FamilyFactorization.cartesianFamilyFactorMap t U.ι zU HW
  have Hα : IsPullback α bZ (pullback.snd t U.ι) zU := Cartesian.FamilyFactorization.cartesianFamilyFactorMap_isPullback t U.ι zU HW
  have HR : IsPullback Y.ι s t U.ι := (isPullback_morphismRestrict t U).flip
  let e := HR.isoPullback
  let β := α ≫ e.inv
  have HF : IsPullback β bZ s zU := by
    apply Hα.of_iso (Iso.refl Z) e.symm (Iso.refl (Spec (.of K))) (Iso.refl U.toScheme)
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id] using HR.isoPullback_inv_snd.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  let cY := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := Y.ι ≫ (t ≫ D.abelian.scheme.hom))
  have hYbase : Y.ι ≫ (t ≫ D.abelian.scheme.hom) = s ≫ pU := by
    rw [← Category.assoc, HR.w, Category.assoc]
  have hcY : cY = Coefficient.ModulePresheaf.schemeCoefficientMap (s ≫ pU) := by
    ext k
    exact congrArg (fun f => f.appTop ((Scheme.ΓSpecIso (.of K)).inv k)) hYbase
  have hI : D.poincareAffineParameterIdeal U.ι = Affine.RationalPointIdeal.affineRationalPointIdeal zU :=
    D.poincareAffineParameterIdeal_eq_rationalPointIdeal U.ι zU hzfac
  let : Algebra K Γ(Z, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap bZ).toAlgebra
  let QY := (ModuleCat.restrictScalars cY).obj
    (ModuleCat.of Γ(Y.toScheme, ⊤) (Γ(Y.toScheme, ⊤) ⧸ (D.poincareAffineParameterIdeal U.ι).map s.appTop.hom))
  let eQ : QY ≅ ModuleCat.of K Γ(Z, ⊤) := by
    dsimp only [QY]
    rw [hcY, hI]
    exact Affine.RationalFiberQuotient.affineRationalFiberQuotientCoefficientIso pU zU hzU HF
  obtain ⟨_, ⟨etop⟩⟩ := A.poincare_finiteFlat_global_cohomology D hg hN hNk t H U hUa hU
  have : IsFinite bZ := inferInstanceAs (IsFinite (pullback.snd t η[D.abelian.scheme].left))
  calc
    _ = Module.finrank K QY := etop.toLinearEquiv.finrank_eq
    _ = Module.finrank K Γ(Z, ⊤) := eQ.toLinearEquiv.finrank_eq
    _ = bZ.finrank (IsLocalRing.closedPoint K) := Finite.FieldCoordinateRank.finiteField_coordinate_finrank bZ (IsLocalRing.closedPoint K)
    _ = _ := Scheme.Hom.finrank_of_isPullback _ _ _ _ HZ (IsLocalRing.closedPoint K)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

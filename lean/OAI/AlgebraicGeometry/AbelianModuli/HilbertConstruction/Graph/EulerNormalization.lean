import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EulerSquareNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BiextensionPoincarePoint

/-! # Euler Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The geometric positivity condition supplies the normalized formula on
the identity base change. It determines the positive graph Euler coefficient,
which then descends from an algebraic closure to every ground field. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_euler_normalized_overAlgClosed [IsAlgClosed k]
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf =
      (2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ) := by
  let f : Spec (.of k) ⟶ Spec (.of k) := 𝟙 _
  let B := A.pullback f
  obtain ⟨L, _, _, ⟨e⟩⟩ := A.polarization.positive k f
  let L₁ := L.pullback (fst B.abelian.scheme B.abelian.scheme).left
  let L₂ := L.pullback (snd B.abelian.scheme B.abelian.scheme).left
  let e' : (((B.dual.poincareAt B.polarization.isogeny.hom).tensor L₁).tensor L₂).sheaf ≅
      (L.pullback μ[B.abelian.scheme].left).sheaf :=
    Tensor.Bifunctor.tensorModuleMapIso (Tensor.Bifunctor.tensorModuleMapIso
      (Polarization.BiextensionPoincarePoint.polarizationBiextensionAt_poincareAtIso A.dual A.polarization.isogeny.hom f)
      (Iso.refl L₁.sheaf)) (Iso.refl L₂.sheaf) ≪≫ e
  have hsq := B.graphBundle_euler_square_of_normalized_formula hg hN hNk L e'
  have hpos := B.graphBundle_euler_pos hN hNk
  have hr : 0 ≤ (2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (Int.natCast_nonneg _)
  have hb : CohomologyEulerCharacteristic.coefficientEulerCharacteristic B.abelian.scheme.hom B.graphBundle.sheaf =
      (2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ) := by nlinarith
  have hunit : IsUnit (N : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of k))))
  have hid : CohomologyEulerCharacteristic.coefficientEulerCharacteristic B.abelian.scheme.hom B.graphBundle.sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf := by
    have h := A.graphBundle_euler_fieldExtension (𝟙 (CommRingCat.of k)) hN hunit
    erw [Spec.map_id] at h
    exact h
  exact hid.symm.trans hb

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_euler_normalized_overField
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf =
      (2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ) := by
  let φ : CommRingCat.of k ⟶ CommRingCat.of (AlgebraicClosure k) :=
    CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))
  let B := A.pullback (Spec.map φ)
  have hNF : (N : AlgebraicClosure k) ≠ 0 := by
    intro hz
    apply hNk
    apply (algebraMap k (AlgebraicClosure k)).injective
    simpa only [map_natCast, map_zero] using hz
  have hunit : IsUnit (N : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of k))))
  exact (A.graphBundle_euler_fieldExtension φ hN hunit).symm.trans
    (B.graphBundle_euler_normalized_overAlgClosed hg hN hNF)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_tensorPower_euler_normalized_overField
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) (m : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf =
      ((2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ)) * (m : ℤ) ^ g := by
  rw [A.graphBundle_tensorPower_euler_overField hN hNk m,
    A.graphBundle_euler_normalized_overField hg hN hNk]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

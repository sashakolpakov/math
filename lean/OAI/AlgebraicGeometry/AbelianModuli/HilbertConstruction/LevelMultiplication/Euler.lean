import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.Euler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.TensorDecomposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerBiproduct

/-! # Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full-level multiplication multiplies genuine Euler characteristic by N^(2g), using actual character line bundles, their homogeneity, and the proved projection formula. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Dual.Data.DualAbelianData.fullLevel_multiplication_pullback_euler
    {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} [NeZero N]
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)
    (level : A.FullLevel N) (L : Line.Bundles.LineBundle A.scheme.left) (hN : (N : K) ≠ 0) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom (L.pullback (A.multiplication N).left).sheaf =
      (N : ℤ) ^ (2 * g) * CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom L.sheaf := by
  classical
  let I := ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ
  let : Fintype I := Fintype.ofFinite I
  let f := (A.multiplication N).left
  let M : I → A.scheme.left.Modules := fun χ =>
    (L.tensor (A.multiplicationCharacterLineBundle level χ hN)).sheaf
  have : IsFinite f := A.fullLevel_multiplication_isFinite level
  have : A.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from A.scheme.hom]; infer_instance⟩
  have : (L.pullback f).sheaf.IsQuasicoherent := (L.pullback f).isQuasicoherent
  have : ∀ χ, (M χ).IsQuasicoherent := fun χ =>
    (L.tensor (A.multiplicationCharacterLineBundle level χ hN)).isQuasicoherent
  have : ∀ χ, (M χ).IsFiniteType := fun χ =>
    (L.tensor (A.multiplicationCharacterLineBundle level χ hN)).isFiniteType
  have hfp : f ≫ A.scheme.hom = A.scheme.hom := (A.multiplication N).w
  have hpush := Affine.PushforwardEuler.coefficientEulerCharacteristic_affinePushforward f A.scheme.hom (L.pullback f).sheaf
  rw [hfp] at hpush
  have hcard : Fintype.card I = N ^ (2 * g) := by
    rw [← Nat.card_eq_fintype_card]
    exact TameCharacters.fullLevelCharacter_card K g N hN
  calc
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom (L.pullback f).sheaf =
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom ((Scheme.Modules.pushforward f).obj (L.pullback f).sheaf) := hpush
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom (⨁ M) :=
      Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso A.scheme.hom
        (A.multiplicationCharacterTensorDecomposition level L hN)
    _ = ∑ χ : I, CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom (M χ) :=
      Proper.CohomologyEulerBiproduct.proper_coherent_euler_biproduct A.scheme.hom M
    _ = ∑ _χ : I, CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom L.sheaf :=
      Finset.sum_congr rfl (fun χ _ => D.multiplicationCharacter_twist_euler level L χ hN)
    _ = (N : ℤ) ^ (2 * g) * CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom L.sheaf := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, Nat.cast_pow]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

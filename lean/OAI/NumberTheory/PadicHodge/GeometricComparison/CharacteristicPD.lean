import OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicForm
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal

/-! # Characteristic PD -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicPD.CharacteristicPDFormPullback

noncomputable section

/-! Killing exact one-forms also kills the original divided-power
forms in every positive degree. -/

open _root_.CategoryTheory

universe u
variable {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}
  {I : Ideal A} {J : Ideal B} {δ : DividedPowers I} {ε : DividedPowers J}
  (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δ ε f.hom.toRingHom)

theorem zero (h : ∀ a : A, KaehlerDifferential.D R B (f a) = 0)
    (n : ℕ) (hn : 0 < n) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf n ω = 0 := by
  obtain ⟨η, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n) ω
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_mk, CharacteristicForm.CharacteristicFormPullback.map_zero f h n hn, map_zero]

theorem power_zero (p : ℕ) (hp : (p : B) = 0) (h : ∀ a : A, ∃ b : B, f a = b ^ p)
    (n : ℕ) (hn : 0 < n) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf n ω = 0 := by
  apply zero f hf _ n hn ω
  intro a
  obtain ⟨b, hb⟩ := h a
  rw [hb, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul B, hp, zero_smul]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicPD.CharacteristicPDFormPullback

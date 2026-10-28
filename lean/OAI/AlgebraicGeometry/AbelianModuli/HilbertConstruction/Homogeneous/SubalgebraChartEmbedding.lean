import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Subalgebra Chart Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.SubalgebraChartEmbedding

noncomputable section

/-! The homogeneous chart of a graded subalgebra embeds in the ambient
localization. This allows polynomial identities to be checked there,
without any reducedness assumption on the coefficient ring. -/
universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (S : Subalgebra R A) (g : ℕ → Submodule R S) [GradedAlgebra g] (f : S)

local instance chartLocalization : IsLocalization.Away (S.val.toRingHom f) (Localization.Away f.val) :=
  inferInstanceAs (IsLocalization.Away f.val (Localization.Away f.val))

def homogeneousSubalgebraChartEmbedding :
    HomogeneousLocalization.Away g f →+* Localization.Away f.val :=
  (IsLocalization.Away.map (Localization.Away f) (Localization.Away f.val) S.val.toRingHom f).comp
    (algebraMap (HomogeneousLocalization.Away g f) (Localization.Away f))

theorem homogeneousSubalgebraChartEmbedding_injective :
    Function.Injective (homogeneousSubalgebraChartEmbedding S g f) := by
  have hmap : Function.Injective
      (IsLocalization.Away.map (Localization.Away f) (Localization.Away f.val) S.val.toRingHom f) := by
    apply (IsLocalization.Away.map_injective_iff (Localization.Away f.val) S.val.toRingHom f).mpr
    intro a ha
    have hz : a = 0 := Subtype.ext ha
    exact ⟨0, by rw [hz, mul_zero]⟩
  exact hmap.comp (HomogeneousLocalization.val_injective _)

theorem homogeneousSubalgebraChartEmbedding_mk {d : ℕ} (hf : f ∈ g d)
    (n : ℕ) (x : S) (hx : x ∈ g (n • d)) :
    homogeneousSubalgebraChartEmbedding S g f (HomogeneousLocalization.Away.mk g hf n x hx) =
      IsLocalization.mk' (M := Submonoid.powers f.val) (Localization.Away f.val) x.val
        ⟨f.val ^ n, ⟨n, rfl⟩⟩ := by
  simp only [homogeneousSubalgebraChartEmbedding, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.Away.map, IsLocalization.map_mk']
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.SubalgebraChartEmbedding

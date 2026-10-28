import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.Grading
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RegradedHomogeneousLocalizationMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.SubalgebraChartEmbedding

/-! # Affine Chart Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.AffineChartEquivalence

noncomputable section

/-! A homogeneous element of Veronese degree d has the same affine
Proj chart before and after regrading. Every fraction lifts explicitly. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) [NeZero N]
variable (f : Subalgebra.veroneseSubalgebra g N)

def veroneseAwayMap : HomogeneousLocalization.Away (Grading.veroneseGrading g N) f →+*
    HomogeneousLocalization.Away g f.val :=
  RegradedHomogeneousLocalizationMap.regradedHomogeneousLocalizationMap (Grading.veroneseGrading g N) g (N * ·)
    (Subalgebra.veroneseSubalgebra g N).val.toRingHom (fun _ _ hx => hx)
    (by rintro x ⟨n, rfl⟩; exact ⟨n, rfl⟩)

theorem veroneseAwayMap_val (x : HomogeneousLocalization.Away (Grading.veroneseGrading g N) f) :
    (veroneseAwayMap g N f x).val =
      Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding (Subalgebra.veroneseSubalgebra g N) (Grading.veroneseGrading g N) f x :=
  RegradedHomogeneousLocalizationMap.regradedHomogeneousLocalizationMap_val _ _ _ _ _ _ x

theorem veroneseAwayMap_injective : Function.Injective (veroneseAwayMap g N f) := by
  intro x y hxy
  apply Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_injective (Subalgebra.veroneseSubalgebra g N) (Grading.veroneseGrading g N) f
  exact (veroneseAwayMap_val g N f x).symm.trans
    ((congrArg HomogeneousLocalization.val hxy).trans (veroneseAwayMap_val g N f y))

theorem veroneseAwayMap_surjective {d : ℕ} (hf : f ∈ Grading.veroneseGrading g N d) :
    Function.Surjective (veroneseAwayMap g N f) := by
  intro x
  obtain ⟨k, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective g hf x
  have ha' : a ∈ g (N * (k * d)) := by
    simpa only [nsmul_eq_mul, Nat.mul_left_comm, Nat.cast_id] using ha
  let a' : Subalgebra.veroneseSubalgebra g N := ⟨a, Subalgebra.veronese_homogeneous_mem g N (k * d) ha'⟩
  have ha'' : a' ∈ Grading.veroneseGrading g N (k • d) := ha'
  refine ⟨HomogeneousLocalization.Away.mk (Grading.veroneseGrading g N) hf k a' ha'', ?_⟩
  apply HomogeneousLocalization.val_injective
  erw [veroneseAwayMap_val, Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_mk]

def veroneseAwayEquiv {d : ℕ} (hf : f ∈ Grading.veroneseGrading g N d) :
    HomogeneousLocalization.Away (Grading.veroneseGrading g N) f ≃+* HomogeneousLocalization.Away g f.val :=
  RingEquiv.ofBijective (veroneseAwayMap g N f)
    ⟨veroneseAwayMap_injective g N f, veroneseAwayMap_surjective g N f hf⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.AffineChartEquivalence

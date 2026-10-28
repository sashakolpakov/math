import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveChartCover

/-! # Projective Comap -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveComap

noncomputable section

/-! Restriction of homogeneous prime ideals defines the point map for
the Veronese comparison. Its behavior on every basic open is explicit. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) [NeZero N]

theorem veroneseProjection_val (n : ℕ) (x : Subalgebra.veroneseSubalgebra g N) :
    ((DirectSum.decompose (Grading.veroneseGrading g N) x n).val).val =
      (DirectSum.decompose g x.val (N * n)).val := by
  let L := (Subalgebra.veroneseSubalgebra g N).val.toLinearMap.comp (GradedAlgebra.proj (Grading.veroneseGrading g N) n)
  let M := (GradedAlgebra.proj g (N * n)).comp (Subalgebra.veroneseSubalgebra g N).val.toLinearMap
  have hLM : L = M := by
    apply DirectSum.decompose_lhom_ext (Grading.veroneseGrading g N)
    intro d
    apply LinearMap.ext
    intro y
    change ((DirectSum.decompose (Grading.veroneseGrading g N) y.val n).val).val =
      (DirectSum.decompose g y.val.val (N * n)).val
    by_cases hdn : d = n
    · subst d
      erw [DirectSum.decompose_of_mem_same (Grading.veroneseGrading g N) y.property,
        DirectSum.decompose_of_mem_same g y.property]
      rfl
    · have hNdn : N * d ≠ N * n := fun he => hdn
        (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne N)) he)
      erw [DirectSum.decompose_of_mem_ne (Grading.veroneseGrading g N) y.property hdn,
        DirectSum.decompose_of_mem_ne g y.property hNdn]
      rfl
  exact LinearMap.congr_fun hLM x

def veroneseHomogeneousIdealComap (I : HomogeneousIdeal g) : HomogeneousIdeal (Grading.veroneseGrading g N) where
  __ := I.toIdeal.comap (Subalgebra.veroneseSubalgebra g N).val.toRingHom
  is_homogeneous' n x hx := by
    change ((DirectSum.decompose (Grading.veroneseGrading g N) x n).val).val ∈ I
    rw [veroneseProjection_val]
    exact I.2 (N * n) hx

def veroneseProjectiveComap (p : ProjectiveSpectrum g) : ProjectiveSpectrum (Grading.veroneseGrading g N) where
  asHomogeneousIdeal := veroneseHomogeneousIdealComap g N p.asHomogeneousIdeal
  isPrime := p.isPrime.comap (Subalgebra.veroneseSubalgebra g N).val.toRingHom
  not_irrelevant_le h := by
    apply p.not_irrelevant_le
    apply (HomogeneousIdeal.irrelevant_le g).mpr
    intro d hd z hz
    have hpow : z ^ N ∈ g (N * d) := by
      simpa only [nsmul_eq_mul, Nat.cast_id] using
        (show z ^ N ∈ g (N • d) from SetLike.pow_mem_graded N (show z ∈ g d from hz))
    let z' : Subalgebra.veroneseSubalgebra g N := ⟨z ^ N, Subalgebra.veronese_homogeneous_mem g N d hpow⟩
    have hz' : z' ∈ HomogeneousIdeal.irrelevant (Grading.veroneseGrading g N) :=
      HomogeneousIdeal.mem_irrelevant_of_mem (Grading.veroneseGrading g N) hd hpow
    exact p.isPrime.mem_of_pow_mem N (h hz')

theorem veroneseProjectiveComap_mem_basicOpen (p : ProjectiveSpectrum g) (f : Subalgebra.veroneseSubalgebra g N) :
    veroneseProjectiveComap g N p ∈ ProjectiveSpectrum.basicOpen (Grading.veroneseGrading g N) f ↔
      p ∈ ProjectiveSpectrum.basicOpen g f.val := Iff.rfl

def veroneseProjectiveContinuousMap : C(ProjectiveSpectrum g, ProjectiveSpectrum (Grading.veroneseGrading g N)) where
  toFun := veroneseProjectiveComap g N
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, ProjectiveSpectrum.isClosed_iff_zeroLocus,
      exists_imp, forall_eq_apply_imp_iff]
    intro s
    refine ⟨(Subalgebra.veroneseSubalgebra g N).val '' s, ?_⟩
    ext p
    change (∀ z ∈ s, z.val ∈ p.asHomogeneousIdeal) ↔
      (∀ z ∈ (Subalgebra.veroneseSubalgebra g N).val '' s, z ∈ p.asHomogeneousIdeal)
    exact Set.forall_mem_image.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveComap

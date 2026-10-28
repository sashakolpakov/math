import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialZeroLocus
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCompactness
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Separation.Hausdorff

/-! # Projective Zero Locus -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus

noncomputable section

/-!
# Hausdorff complex projective space and closed homogeneous zero loci

The topology is the quotient of ordinary complex coordinates on nonzero vectors.
The projective equality relation is closed because it is cut out by the two-by-two
coordinate minors. The quotient map is open, so the quotient is Hausdorff.
Homogeneous equations descend through the actual projectivization quotient, and
their zero loci are closed for this ordinary topology.

No identification with a projective scheme's complex points is asserted here.
-/

open _root_.Topology

variable {ι : Type*}

private def nonzeroComplexScale (a : ℂˣ) (v : {v : ι → ℂ // v ≠ 0}) :
    {v : ι → ℂ // v ≠ 0} :=
  ⟨a • v.val, (smul_ne_zero_iff_ne a).mpr v.property⟩

private theorem continuous_nonzeroComplexScale (a : ℂˣ) :
    Continuous (nonzeroComplexScale (ι := ι) a) := by
  apply Continuous.subtype_mk
  exact (continuous_const_smul a).comp continuous_subtype_val

/-- Saturation of an open set of nonzero vectors is open, so projection to
complex projective space is an open map. -/
theorem isOpenMap_projectivization_mk' :
    IsOpenMap (Projectivization.mk' ℂ : {v : ι → ℂ // v ≠ 0} →
      Projectivization ℂ (ι → ℂ)) := by
  intro U hU
  change IsOpen ((Projectivization.mk' ℂ) ⁻¹' ((Projectivization.mk' ℂ) '' U))
  have hs : (Projectivization.mk' ℂ) ⁻¹' ((Projectivization.mk' ℂ) '' U) =
      ⋃ a : ℂˣ, (nonzeroComplexScale a) ⁻¹' U := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, heq⟩
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ w.val v.val w.property v.property).mp heq
      refine ⟨a, ?_⟩
      have hh : nonzeroComplexScale a v = w := Subtype.ext ha
      rw [hh]
      exact hw
    · rintro ⟨a, ha⟩
      refine ⟨nonzeroComplexScale a v, ha, ?_⟩
      exact (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr ⟨a, rfl⟩
  rw [hs]
  exact isOpen_iUnion fun a => hU.preimage (continuous_nonzeroComplexScale a)

/-- Two nonzero complex coordinate vectors represent the same projective point
exactly when all their two-by-two coordinate minors vanish. -/
theorem projectivization_mk_eq_iff_minors_eq (v w : ι → ℂ)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw ↔
      ∀ i j, v i * w j = v j * w i := by
  constructor
  · intro h i j
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ v w hv hw).mp h
    rw [← ha]
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul]
    simp only [mul_comm, mul_left_comm]
  · intro h
    have hex : ∃ i, w i ≠ 0 := by
      by_contra hn
      apply hw
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr
    refine ⟨v i / w i, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    exact (div_eq_iff hi).mpr (h i j)

/-- Equality after projectivization is a closed relation on nonzero vectors. -/
theorem isClosed_projectiveEquality :
    IsClosed {q : {v : ι → ℂ // v ≠ 0} × {v : ι → ℂ // v ≠ 0} |
      Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2} := by
  have heq : {q : {v : ι → ℂ // v ≠ 0} × {v : ι → ℂ // v ≠ 0} |
      Projectivization.mk' ℂ q.1 = Projectivization.mk' ℂ q.2} =
      ⋂ i, ⋂ j, {q | q.1.val i * q.2.val j = q.1.val j * q.2.val i} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact projectivization_mk_eq_iff_minors_eq q.1.val q.2.val q.1.property q.2.property
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq
    (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)))
    (((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))

/-- The ordinary projection of nonzero complex vectors is an open quotient map. -/
theorem isOpenQuotientMap_projectivization_mk' :
    IsOpenQuotientMap (Projectivization.mk' ℂ : {v : ι → ℂ // v ≠ 0} →
      Projectivization ℂ (ι → ℂ)) :=
  ⟨(ProjectiveCompactness.isQuotientMap_projectivization_mk' ℂ (ι → ℂ)).surjective,
    ProjectiveCompactness.continuous_projectivization_mk' ℂ (ι → ℂ), isOpenMap_projectivization_mk'⟩

/-- Complex projective space is Hausdorff for the ordinary quotient topology. -/
instance projectivization_t2Space : T2Space (Projectivization ℂ (ι → ℂ)) :=
  (t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_projectivization_mk').mpr
    isClosed_projectiveEquality

/-- A homogeneous complex polynomial has a closed projective zero locus in the
ordinary quotient topology. -/
theorem isClosed_homogeneousProjectiveZeroLocus (f : MvPolynomial ι ℂ) {d : ℕ}
    (hf : f.IsHomogeneous d) : IsClosed (Foundations.Scheme.ProjectiveZeroLocus.homogeneousProjectiveZeroLocus f hf) := by
  rw [ProjectiveCompactness.isClosed_projectivization_iff ℂ (ι → ℂ)]
  change IsClosed {v : {v : ι → ℂ // v ≠ 0} | MvPolynomial.eval v.val f = 0}
  exact (PolynomialZeroLocus.isClosed_mvPolynomial_zeroSet f).preimage continuous_subtype_val

/-- Arbitrarily many homogeneous equations cut out a closed complex projective
locus in the ordinary quotient topology. -/
theorem isClosed_projectiveCommonZeroLocus {κ : Type*} (f : κ → MvPolynomial ι ℂ)
    (d : κ → ℕ) (hf : ∀ k, (f k).IsHomogeneous (d k)) :
    IsClosed (Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus f d hf) :=
  isClosed_iInter fun k => isClosed_homogeneousProjectiveZeroLocus (f k) (hf k)

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus

import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Integral Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.IntegralTopology.ClosednessConstruction

/-! Closedness: compactness estimates for integral maps of affine complex points. -/

open scoped _root_.Polynomial NNReal

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- All evaluations together form a closed embedding of complex characters. -/
theorem isClosedEmbedding_character_evaluations :
    Topology.IsClosedEmbedding (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B => (x : B → ℂ)) := by
  have hs : Function.Surjective
      (MvPolynomial.aeval (id : B → B) : MvPolynomial B ℂ →ₐ[ℂ] B) := by
    intro b
    exact ⟨MvPolynomial.X b, MvPolynomial.aeval_X _ _⟩
  simpa only [MvPolynomial.aeval_X, id_eq] using
    Analytic.FiniteTypeAffineTopology.isClosedEmbedding_polynomialPresentation
      (MvPolynomial.aeval (id : B → B)) hs

/-- Specializing a monic equation over a compact set gives a uniform root bound. -/
theorem monic_specialization_root_bound (p : A[X]) (hp : p.Monic)
    (K : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) (hK : IsCompact K) :
    ∃ M : ℝ≥0, ∀ x ∈ K, ∀ z : ℂ,
      (p.map x.toRingHom).IsRoot z → ‖z‖₊ ≤ M := by
  let b : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → ℝ≥0 := fun x =>
    (Finset.range p.natDegree).sup (fun j => ‖x (p.coeff j)‖₊) + 1
  have hb : Continuous b :=
    (Continuous.finset_sup_apply (fun j _ =>
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (p.coeff j)).nnnorm)).add continuous_const
  obtain ⟨M, hM⟩ := (hK.image hb).bddAbove
  refine ⟨M, fun x hx z hz => ?_⟩
  have hbound := hz.norm_lt_cauchyBound (hp.map x.toRingHom).ne_zero
  have hcb : (p.map x.toRingHom).cauchyBound = b x := by
    simp only [Polynomial.cauchyBound, hp.natDegree_map,
      (hp.map x.toRingHom).leadingCoeff, nnnorm_one, div_one,
      Polynomial.coeff_map, b]
    rfl
  rw [hcb] at hbound
  exact hbound.le.trans (hM ⟨x, hx, rfl⟩)

/-- Integral coordinates remain uniformly bounded over a compact set of base points. -/
theorem integral_coordinate_bound (f : A →ₐ[ℂ] B) (hf : f.toRingHom.IsIntegral)
    (K : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) (hK : IsCompact K) (b : B) :
    ∃ M : ℝ≥0, ∀ x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x ∈ K → ‖x b‖₊ ≤ M := by
  obtain ⟨p, hp, heq⟩ := hf b
  obtain ⟨M, hM⟩ := monic_specialization_root_bound p hp K hK
  refine ⟨M, fun x hx => hM (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) hx (x b) ?_⟩
  change (p.map (x.comp f).toRingHom).eval (x b) = 0
  rw [Polynomial.eval_map]
  change p.eval₂ (x.toRingHom.comp f.toRingHom) (x b) = 0
  exact (Polynomial.hom_eval₂ p f.toRingHom x.toRingHom b).symm.trans
    ((congrArg x.toRingHom heq).trans (map_zero _))

/-- Integral affine maps have compact inverse images of compact sets of complex points. -/
theorem integral_comap_isCompact_preimage
    (f : A →ₐ[ℂ] B) (hf : f.toRingHom.IsIntegral)
    (K : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) (hK : IsCompact K) :
    IsCompact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f ⁻¹' K) := by
  classical
  choose M hM using integral_coordinate_bound f hf K hK
  have hc : IsCompact (Set.pi Set.univ (fun b : B => Metric.closedBall (0 : ℂ) (M b))) :=
    isCompact_univ_pi (fun b => isCompact_closedBall (0 : ℂ) (M b))
  have hpre := (isClosedEmbedding_character_evaluations (B := B)).isCompact_preimage hc
  apply hpre.of_isClosed_subset (hK.isClosed.preimage (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f).continuous)
  intro x hx b _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact_mod_cast hM b x hx

/-- Over a finite-type complex base algebra, an integral map induces a proper
map for the ordinary topology on complex characters. -/
theorem integral_comap_isProperMap [Algebra.FiniteType ℂ A]
    (f : A →ₐ[ℂ] B) (hf : f.toRingHom.IsIntegral) : IsProperMap (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f).continuous, fun K hK => integral_comap_isCompact_preimage f hf K hK⟩

end OAI.AlgebraicGeometry.ComplexPoints.IntegralTopology.ClosednessConstruction

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.TensorCechVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorZeroCoproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistCover

/-! # Cover Tensor Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The finite source of the constructed negative-twist quotient has uniformly vanishing positive Čech cohomology after large tensor twists. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)} {M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules}

theorem Projective.NegativeTwistCover.ProjectiveNegativeTwistCover.source_tensorCech_eventually_vanish (D : Projective.NegativeTwistCover.ProjectiveNegativeTwistCover I M) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ q : ℕ,
      IsZero ((Projective.TwistedCech.projectiveTwistedCech I D.source d).homology (q + 1)) := by
  classical
  let : Fintype D.index := @Fintype.ofFinite D.index D.finite
  obtain ⟨B, hB⟩ := PositiveTwist.CechVanishing.positiveTwistCech_eventually_vanish I
  refine ⟨Finset.univ.sup D.degree + B, fun d hd q ↦ ?_⟩
  let F : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules ⥤ ModuleCat.{u} R :=
    Projective.TwistedCech.projectiveTwistedCechFunctor I d ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) (q + 1)
  have : F.Additive := by dsimp [F]; infer_instance
  apply HilbertConstruction.Additive.FunctorZeroCoproducts.additive_functor_zero_coproduct F (fun i : D.index ↦ (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (D.degree i)).sheaf)
  intro i
  have hi : D.degree i ≤ Finset.univ.sup D.degree := Finset.le_sup (Finset.mem_univ i)
  exact NegativeTwist.TensorCechVanishing.negativeTwist_tensorCech_vanish_of_bound I B hB (D.degree i) d
    ((Nat.add_le_add_right hi B).trans hd) q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

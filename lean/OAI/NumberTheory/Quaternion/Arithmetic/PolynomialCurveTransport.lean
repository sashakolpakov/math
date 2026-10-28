import OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialCurves
import OAI.NumberTheory.Quaternion.Arithmetic.ApproximationTopology
import OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicHypotheses

/-! # Polynomial Curve Transport -/

namespace OAI

noncomputable section

namespace NumberTheory.Quaternion.Arithmetic.PolynomialCurveTransport

/-! Strong approximation follows directly from local generation by
polynomial additive curves defined over the number field. This criterion
does not assume an arithmetic quotient measure. -/

open scoped Classical
open Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def groundFieldCurveElements (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : LocalAdeles.Place F) : Set (LocalAdeles.LocalPoints G v) :=
  {g | ∃ (u : PolynomialAdditiveCurves.PolynomialAdditiveCurve G) (t : LocalAdeles.Completion v),
    u.hom _ (LocalAdeles.localEmbedding v) (Multiplicative.ofAdd t) = g}

theorem strongApproximation_of_groundField_curve_generation (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
    (hgen : ∀ v : ApproximationTopology.AwayPlace S, Subgroup.closure (groundFieldCurveElements G v.val) = ⊤) :
    DenseRange (LocalAdeles.diagonalAway G S) := by
  let H := (LocalAdeles.diagonalAway G S).range.topologicalClosure
  have htop : H = ⊤ := by
    apply ApproximationTopology.adelic_closed_subgroup_eq_top_of_single G S H
      (LocalAdeles.diagonalAway G S).range.isClosed_topologicalClosure
    intro v g
    have hle : Subgroup.closure (groundFieldCurveElements G v.val) ≤
        H.comap (ApproximationTopology.awayMulSingleHom G S v) := by
      apply (Subgroup.closure_le (H.comap (ApproximationTopology.awayMulSingleHom G S v))).mpr
      rintro x ⟨u, t, rfl⟩
      exact AdelicPolynomialCurves.supported_polynomial_curve_mem_diagonal_closure G S harch u v t
    rw [hgen v] at hle
    exact hle (Subgroup.mem_top g)
  intro a
  change a ∈ H
  rw [htop]
  exact Subgroup.mem_top a

end NumberTheory.Quaternion.Arithmetic.PolynomialCurveTransport

namespace NumberTheory.Quaternion.Arithmetic

/-! Polynomial group homomorphisms transport ground-field additive
curves, and surjective local homomorphisms transport their generation. -/

open scoped Classical

variable {F : Type} [Field F] {m n : ℕ}
  {H : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F m} {G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n}

def AlgebraicHypotheses.PolynomialHom.mapAdditiveCurve (f : AlgebraicHypotheses.PolynomialHom H G) (u : PolynomialAdditiveCurves.PolynomialAdditiveCurve H) :
    PolynomialAdditiveCurves.PolynomialAdditiveCurve G where
  coordinates i j := MvPolynomial.eval₂Hom Polynomial.C
    (fun ij => u.coordinates ij.1 ij.2) (f.coordinates i j)
  hom K _ ρ := (f.hom K ρ).comp (u.hom K ρ)
  coordinate_eq K _ ρ t i j := by
    change (f.hom K ρ (u.hom K ρ (Multiplicative.ofAdd t))).val i j = _
    rw [f.coordinate_eq]
    have he : (Polynomial.eval₂RingHom ρ t).comp
        (MvPolynomial.eval₂Hom Polynomial.C (fun ij => u.coordinates ij.1 ij.2)) =
        ArithmeticGroups.Lattices.Algebraic.evaluateMatrix ρ (u.hom K ρ (Multiplicative.ofAdd t)).val := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
      · intro ij
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X',
          Polynomial.coe_eval₂RingHom, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
        exact (u.coordinate_eq K ρ t ij.1 ij.2).symm
    exact (RingHom.congr_fun he (f.coordinates i j)).symm

variable [NumberField F]

theorem AlgebraicHypotheses.PolynomialHom.map_groundFieldCurveElements (f : AlgebraicHypotheses.PolynomialHom H G) (v : LocalAdeles.Place F)
    {g : LocalAdeles.LocalPoints H v} (hg : g ∈ PolynomialCurveTransport.groundFieldCurveElements H v) :
    f.hom _ (LocalAdeles.localEmbedding v) g ∈ PolynomialCurveTransport.groundFieldCurveElements G v := by
  rcases hg with ⟨u, t, rfl⟩
  exact ⟨f.mapAdditiveCurve u, t, rfl⟩

theorem AlgebraicHypotheses.PolynomialHom.groundField_curve_generation (f : AlgebraicHypotheses.PolynomialHom H G) (v : LocalAdeles.Place F)
    (hf : Function.Surjective (f.hom _ (LocalAdeles.localEmbedding v)))
    (hH : Subgroup.closure (PolynomialCurveTransport.groundFieldCurveElements H v) = ⊤) :
    Subgroup.closure (PolynomialCurveTransport.groundFieldCurveElements G v) = ⊤ := by
  let C := Subgroup.closure (PolynomialCurveTransport.groundFieldCurveElements G v)
  have hle : Subgroup.closure (PolynomialCurveTransport.groundFieldCurveElements H v) ≤
      C.comap (f.hom _ (LocalAdeles.localEmbedding v)) := by
    apply (Subgroup.closure_le (C.comap (f.hom _ (LocalAdeles.localEmbedding v)))).mpr
    intro g hg
    exact Subgroup.subset_closure (f.map_groundFieldCurveElements v hg)
  rw [hH] at hle
  apply top_unique
  intro g _
  obtain ⟨h, rfl⟩ := hf g
  exact hle (Subgroup.mem_top h)

theorem PolynomialCurveTransport.strongApproximation_of_polynomial_surjection (f : AlgebraicHypotheses.PolynomialHom H G)
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
    (hf : ∀ v : ApproximationTopology.AwayPlace S, Function.Surjective (f.hom _ (LocalAdeles.localEmbedding v.val)))
    (hH : ∀ v : ApproximationTopology.AwayPlace S, Subgroup.closure (PolynomialCurveTransport.groundFieldCurveElements H v.val) = ⊤) :
    DenseRange (LocalAdeles.diagonalAway G S) :=
  PolynomialCurveTransport.strongApproximation_of_groundField_curve_generation G S harch
    (fun v => f.groundField_curve_generation v.val (hf v) (hH v))

end NumberTheory.Quaternion.Arithmetic

end

end OAI

import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth

/-! # Dolbeault Local -/

namespace OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal

noncomputable section

/-!
The local Dolbeault operators on actual complex-valued real differential forms.
They are obtained by alternating the complex-linear and conjugate-linear parts
of the real Fréchet derivative. Their bidegree is verified against every
nonzero complex scalar, with purity required only near the point considered.
-/

open Filter
open scoped ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {n p q : ℕ}

/-- The local `d'` operator: alternate the complex-linear derivative part. -/
def extDerivPrime (form : Basic.RawForm E n) (x : E) : Basic.FormValue E (n + 1) :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    (ComplexDerivativeParts.complexLinearPartCLM E (Basic.FormValue E n) (fderiv ℝ form x))

/-- The local `d''` operator: alternate the conjugate-linear derivative part. -/
def extDerivDoublePrime (form : Basic.RawForm E n) (x : E) : Basic.FormValue E (n + 1) :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    (ComplexDerivativeParts.complexAntilinearPartCLM E (Basic.FormValue E n) (fderiv ℝ form x))

/-- Their sum is exactly the ordinary exterior derivative. -/
theorem extDerivPrime_add_extDerivDoublePrime (form : Basic.RawForm E n) (x : E) :
    extDerivPrime form x + extDerivDoublePrime form x = extDeriv form x := by
  rw [extDerivPrime, extDerivDoublePrime,
    ← ContinuousAlternatingMap.alternatizeUncurryFin_add, ComplexDerivativeParts.complexDerivativeParts_add]
  rfl

/-- Splitting the new derivative slot preserves the old covector bidegree. -/
theorem complexLinearPartCLM_hasBidegree
    (D : E →L[ℝ] Basic.FormValue E (p + q))
    (hD : ∀ u : E, Bidegree.HasBidegree E p q (D u)) (u : E) :
    Bidegree.HasBidegree E p q (ComplexDerivativeParts.complexLinearPartCLM E (Basic.FormValue E (p + q)) D u) := by
  rw [ComplexDerivativeParts.complexLinearPartCLM_apply]
  exact (Bidegree.pureBidegreeSubmodule E p q).smul_mem _
    ((Bidegree.pureBidegreeSubmodule E p q).sub_mem (hD u)
      ((Bidegree.pureBidegreeSubmodule E p q).smul_mem _ (hD (Complex.I • u))))

/-- The conjugate-linear split also preserves the old covector bidegree. -/
theorem complexAntilinearPartCLM_hasBidegree
    (D : E →L[ℝ] Basic.FormValue E (p + q))
    (hD : ∀ u : E, Bidegree.HasBidegree E p q (D u)) (u : E) :
    Bidegree.HasBidegree E p q (ComplexDerivativeParts.complexAntilinearPartCLM E (Basic.FormValue E (p + q)) D u) := by
  rw [ComplexDerivativeParts.complexAntilinearPartCLM_apply]
  exact (Bidegree.pureBidegreeSubmodule E p q).smul_mem _
    ((Bidegree.pureBidegreeSubmodule E p q).add_mem (hD u)
      ((Bidegree.pureBidegreeSubmodule E p q).smul_mem _ (hD (Complex.I • u))))

/-- The holomorphic character acquires one factor of the scalar. -/
theorem bidegreeCharacter_succ_left (p q : ℕ) (z : ℂˣ) :
    Bidegree.bidegreeCharacter (p + 1) q z = (z : ℂ) * Bidegree.bidegreeCharacter p q z := by
  simp only [Bidegree.bidegreeCharacter, pow_succ]
  ring

/-- The antiholomorphic character acquires one conjugate scalar factor. -/
theorem bidegreeCharacter_succ_right (p q : ℕ) (z : ℂˣ) :
    Bidegree.bidegreeCharacter p (q + 1) z = star (z : ℂ) * Bidegree.bidegreeCharacter p q z := by
  simp only [Bidegree.bidegreeCharacter, pow_succ]
  ring

/-- `d'` raises the holomorphic degree, with the full scalar-character meaning
of bidegree. The tuple length is written without a degree-transport cast. -/
theorem extDerivPrime_bidegree_character
    {form : Basic.RawForm E (p + q)} {x : E}
    (hform : DifferentiableAt ℝ form x)
    (hpure : ∀ᶠ y in 𝓝 x, Bidegree.HasBidegree E p q (form y))
    (z : ℂˣ) (v : Fin (p + q + 1) → E) :
    extDerivPrime form x (fun i => (z : ℂ) • v i) =
      Bidegree.bidegreeCharacter (p + 1) q z * extDerivPrime form x v := by
  rw [bidegreeCharacter_succ_left]
  apply DolbeaultCoefficientType.alternatizeUncurryFin_scaling
  · intro u
    exact ComplexDerivativeParts.complexLinearPartCLM_apply_smul E (Basic.FormValue E (p + q))
      (fderiv ℝ form x) (z : ℂ) u
  · intro u w
    exact complexLinearPartCLM_hasBidegree (fderiv ℝ form x)
      (DolbeaultCoefficientType.fderiv_hasBidegree hform hpure) u z w

/-- `d''` raises the antiholomorphic degree, again for every nonzero scalar. -/
theorem extDerivDoublePrime_bidegree_character
    {form : Basic.RawForm E (p + q)} {x : E}
    (hform : DifferentiableAt ℝ form x)
    (hpure : ∀ᶠ y in 𝓝 x, Bidegree.HasBidegree E p q (form y))
    (z : ℂˣ) (v : Fin (p + q + 1) → E) :
    extDerivDoublePrime form x (fun i => (z : ℂ) • v i) =
      Bidegree.bidegreeCharacter p (q + 1) z * extDerivDoublePrime form x v := by
  rw [bidegreeCharacter_succ_right]
  apply DolbeaultCoefficientType.alternatizeUncurryFin_scaling
  · intro u
    exact ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul E (Basic.FormValue E (p + q))
      (fderiv ℝ form x) (z : ℂ) u
  · intro u w
    exact complexAntilinearPartCLM_hasBidegree (fderiv ℝ form x)
      (DolbeaultCoefficientType.fderiv_hasBidegree hform hpure) u z w

end

end OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal

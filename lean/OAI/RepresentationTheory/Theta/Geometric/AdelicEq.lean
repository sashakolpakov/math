import OAI.RepresentationTheory.Theta.Geometric.No

/-! # Adelic Eq -/

namespace OAI.RepresentationTheory.Theta.Geometric.AdelicEq.Adelic

noncomputable section

/-!
# The period/lattice quotient used by GeometricTheta

This constructs G(Q)\(D × G(A_f)/K) as an actual quotient. The finite coset
is the marked lattice datum. The identities below are proved from the
quotient relation, not supplied as a branch-compatibility field.
-/

variable {GQ Gf B : Type*} [Group GQ] [Group Gf] [MulAction GQ B]

def periodLatticeSetoid (qf : GQ →* Gf) (K : Subgroup Gf) :
    Setoid (B × (Gf ⧸ K)) where
  r x y := ∃ γ : GQ, y.1 = γ • x.1 ∧ y.2 = qf γ • x.2
  iseqv := {
    refl := fun x => ⟨1, by simp, by simp⟩
    symm := by
      rintro x y ⟨γ, hB, hf⟩
      refine ⟨γ⁻¹, ?_, ?_⟩
      · rw [hB, inv_smul_smul]
      · rw [hf, map_inv, inv_smul_smul]
    trans := by
      rintro x y z ⟨γ, hB, hf⟩ ⟨δ, hB', hf'⟩
      refine ⟨δ * γ, ?_, ?_⟩
      · rw [hB', hB, mul_smul]
      · rw [hf', hf, map_mul, mul_smul] }

def PeriodLatticeQuotient (qf : GQ →* Gf) (K : Subgroup Gf) :=
  Quotient (periodLatticeSetoid (B := B) qf K)

def point (qf : GQ →* Gf) (K : Subgroup Gf) (L : B) (g : Gf) :
    PeriodLatticeQuotient (B := B) qf K :=
  Quotient.mk _ (L, QuotientGroup.mk g)

/-- Rational transport preserves the period/lattice point. -/
theorem point_rational (qf : GQ →* Gf) (K : Subgroup Gf)
    (γ : GQ) (L : B) (g : Gf) :
    point qf K L g = point qf K (γ • L) (qf γ * g) := by
  apply Quotient.sound
  exact ⟨γ, rfl, rfl⟩

/-- The lattice level, including the away marking, acts trivially. -/
theorem point_level (qf : GQ →* Gf) (K : Subgroup Gf)
    (L : B) (g k : Gf) (hk : k ∈ K) :
    point qf K L (g * k) = point qf K L g := by
  have heq : (QuotientGroup.mk (g * k) : Gf ⧸ K) = QuotientGroup.mk g := by
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using K.inv_mem hk
  exact congrArg (fun c : Gf ⧸ K => Quotient.mk (periodLatticeSetoid qf K) (L, c)) heq

/-- A representative in the prescribed finite left coset realizes the
branch by its genuine rational period action. -/
theorem branch_eq_rational_period
    (qf : GQ →* Gf) (K : Subgroup Gf) (g : Gf) (γ : GQ)
    (hcoset : qf γ * g⁻¹ ∈ K) (L : B) :
    point qf K L g⁻¹ = point qf K (γ • L) 1 := by
  rw [point_rational qf K γ L g⁻¹]
  simpa only [one_mul] using point_level qf K (γ • L) 1 _ hcoset

variable {Gq Ga : Type*}
  [Group Gq] [TopologicalSpace Gq] [IsTopologicalGroup Gq]
  [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]

/-- Arithmetic gives the actual branch formula in the constructed adelic quotient.
The period action and the prescribed away marking are retained exactly. -/
theorem active_branch_of_Arithmetic
    (qf : GQ →* Gq × Ga)
    (h_Arithmetic : DenseRange qf)
    (Kq : OpenSubgroup Gq) (Ka : OpenSubgroup Ga) (g : Gq) :
    ∃ γ : GQ,
      (qf γ).1 * g⁻¹ ∈ Kq ∧ (qf γ).2 ∈ Ka ∧
      ∀ L : B,
        point qf (Kq.toSubgroup.prod Ka.toSubgroup) L (g⁻¹, 1) =
          point qf (Kq.toSubgroup.prod Ka.toSubgroup) (γ • L) 1 := by
  obtain ⟨γ, hq, ha⟩ := No.rational_representative_of_Arithmetic qf h_Arithmetic Kq Ka g
  refine ⟨γ, hq, ha, ?_⟩
  intro L
  have hcoset : qf γ * (g, (1 : Ga))⁻¹ ∈ Kq.toSubgroup.prod Ka.toSubgroup := by
    exact ⟨hq, by simpa using ha⟩
  simpa using branch_eq_rational_period qf
    (Kq.toSubgroup.prod Ka.toSubgroup) (g, (1 : Ga)) γ hcoset L

end

end OAI.RepresentationTheory.Theta.Geometric.AdelicEq.Adelic

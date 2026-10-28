import OAI.RepresentationTheory.Theta.Geometric.Reference.LocalBasis
import OAI.RepresentationTheory.Theta.Geometric.Local.TraceIntegrality
import OAI.RepresentationTheory.Theta.Geometric.Reference.PolarizationMultiple

/-! # Trace B -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Every integral local functional, multiplied by the original product
of polarization divisors, is represented by the completed polarization. -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.localTracePairing_integral_reference (x y : D.pel.reference.lattice) :
    D.localTracePairing (D.jointLocalEmbedding x.val) (D.jointLocalEmbedding y.val) =
      (D.pel.reference.integralForm x y : ℚ_[q]) := by
  rw [D.localTracePairing_reference hc hgood hdegree]
  have htrace : (D.pel.reference.integralForm x y : ℚ) = D.pel.reference.traceForm x y := by
    rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h x y
  rw [← htrace, map_intCast]

include hc in
theorem Data.ActiveHeckeThetaData.localTracePairing_multiple_basis (i : Fin (2 * (3 * s))) :
    ∃ u : D.pel.reference.lattice, ∀ j : Fin (2 * (3 * s)),
      D.localTracePairing (D.jointLocalEmbedding u.val) (D.jointQBasis hg hdegree hgood j) =
        if j = i then (∏ k, D.pel.reference.polarizationType k : ℚ_[q]) else 0 := by
  let b := D.pel.reference.referenceBasis hg.reference_admissible
  have htype : D.pel.reference.HasPolarizationType := by
    rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨u, hu⟩ := Reference.PolarizationMultiple.referenceIntegralForm_multiple D.pel.reference htype (b.coord i)
  refine ⟨u, fun j => ?_⟩
  rw [D.jointQBasis_apply hg hdegree hc hgood,
    D.localTracePairing_integral_reference hg hc hgood hdegree]
  have he := LinearMap.congr_fun hu (b j)
  have he' := congrArg (fun z : ℤ => (z : ℚ_[q])) he
  simpa [b, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    eq_comm] using he'

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.localTracePairing_multiple_functional
    (f : (Fin s × Bool → Fin 3 → ℚ_[q]) →ₗ[ℚ_[q]] ℚ_[q])
    (hf : ∀ w ∈ D.jointLocalLattice, ‖f w‖ ≤ 1) :
    ∃ u ∈ D.jointLocalLattice, ∀ y,
      D.localTracePairing u y = (∏ k, D.pel.reference.polarizationType k : ℚ_[q]) * f y := by
  let b := D.jointQBasis hg hdegree hgood
  choose u hu using D.localTracePairing_multiple_basis hg hc hgood hdegree
  let a (i : Fin (2 * (3 * s))) : ℤ_[q] :=
    ⟨f (b i), hf (b i) (D.jointQBasis_mem hg hdegree hc hgood i)⟩
  let w := ∑ i, (a i : ℚ_[q]) • D.jointLocalEmbedding (u i).val
  have hw : w ∈ D.jointLocalLattice := by
    apply D.jointLocalLattice.sum_mem
    intro i _
    change a i • D.jointLocalEmbedding (u i).val ∈ D.jointLocalLattice
    exact D.jointLocalLattice.smul_mem (a i) (Submodule.subset_span ⟨_, (u i).property, rfl⟩)
  have he : D.localTracePairing w = (∏ k, D.pel.reference.polarizationType k : ℚ_[q]) • f := by
    apply b.ext
    intro j
    change D.localTracePairing (∑ i, (a i : ℚ_[q]) • D.jointLocalEmbedding (u i).val) (b j) = _
    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smul₂, smul_eq_mul, b, hu]
    simp [a, b, mul_comm]
  refine ⟨w, hw, fun y => ?_⟩
  exact LinearMap.congr_fun he y

end

section

/-! The prescribed polarization type is prime to q, so every local
diagonal pairing coefficient is a q-adic unit. In particular the original
Hermitian coefficient b is a unit in every supplied local embedding. -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.localOpposite_eq_iff (v w : Fin s × Bool) :
    (v.1, !v.2) = (w.1, !w.2) ↔ v = w := by
  rcases v with ⟨v, b⟩
  rcases w with ⟨w, c⟩
  cases b <;> cases c <;> simp

theorem Data.ActiveHeckeThetaData.localTracePairing_unit_right (v : Fin s × Bool) (i : Fin 3)
    (x : Fin s × Bool → Fin 3 → ℚ_[q]) :
    D.localTracePairing x (Pi.single (v.1, !v.2) (Pi.single i 1)) =
      D.localTraceCoefficient v i * x v i := by
  simp [D.localTracePairing_apply, Pi.single_apply, ite_apply]
  simp only [← Prod.mk.injEq]
  simp

theorem Data.ActiveHeckeThetaData.localTraceCoefficient_unit (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (v : Fin s × Bool) (i : Fin 3) : ‖D.localTraceCoefficient v i‖ = 1 := by
  let f : (Fin s × Bool → Fin 3 → ℚ_[q]) →ₗ[ℚ_[q]] ℚ_[q] := Data.ActiveHeckeThetaData.localCoordinate (v.1, !v.2) i
  have hf (x) (hx : x ∈ D.jointLocalLattice) : ‖f x‖ ≤ 1 :=
    (Local.MatrixLattice.standardLocalLattice_mem_iff q _).mp ((D.jointLocalLattice_standard hg hc hgood x).mp hx (v.1, !v.2)) i
  obtain ⟨x, hx, hp⟩ := D.localTracePairing_multiple_functional hg hc hgood hdegree f hf
  have he := hp (Pi.single (v.1, !v.2) (Pi.single i 1))
  rw [D.localTracePairing_unit_right] at he
  have hf1 : f (Pi.single (v.1, !v.2) (Pi.single i 1)) = 1 := by
    change (Pi.single (v.1, !v.2) (Pi.single i (1 : ℚ_[q])) :
      Fin s × Bool → Fin 3 → ℚ_[q]) (v.1, !v.2) i = 1
    rw [Pi.single_eq_same, Pi.single_eq_same]
  rw [hf1, mul_one] at he
  have hm : ‖(∏ k, D.pel.reference.polarizationType k : ℚ_[q])‖ = 1 := by
    rw [← Nat.cast_prod]
    exact Padic.norm_natCast_eq_one_iff.mpr hgood.2.2.2.2
  have hxnorm : ‖x v i‖ ≤ 1 :=
    (Local.MatrixLattice.standardLocalLattice_mem_iff q _).mp ((D.jointLocalLattice_standard hg hc hgood x).mp hx v) i
  apply le_antisymm (D.localTraceCoefficient_integral hg hc hgood hdegree v i)
  calc
    1 = ‖D.localTraceCoefficient v i‖ * ‖x v i‖ := by rw [← norm_mul, he, hm]
    _ ≤ ‖D.localTraceCoefficient v i‖ * 1 := mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _)
    _ = ‖D.localTraceCoefficient v i‖ := mul_one _

theorem Data.ActiveHeckeThetaData.localEmbedding_b_norm (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (v : Fin s × Bool) : ‖D.localEmbedding v D.pel.reference.b‖ = 1 := by
  have he : D.localTraceCoefficient v 2 =
      D.localTraceCoefficient v 0 * D.localEmbedding v D.pel.reference.b := by
    simp [Data.ActiveHeckeThetaData.localTraceCoefficient]
  have hn := congrArg (fun z : ℚ_[q] => ‖z‖) he
  rw [D.localTraceCoefficient_unit hg hc hgood hdegree, norm_mul,
    D.localTraceCoefficient_unit hg hc hgood hdegree, one_mul] at hn
  exact hn.symm

end

/-! The conjugate local matrix is the adjoint of the inverse. Because
the original Hermitian coefficients are q-adic units, integrality of one
local side implies integrality of its conjugate side. -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.rationalUnitary_opposite_entry (g : D.RationalSU) (i j : Fin 3) :
    (if i = 2 then D.pel.reference.b else 1) *
      NumberField.IsCMField.complexConj E (g.val.val i j) =
    (if j = 2 then D.pel.reference.b else 1) * (g⁻¹).val.val j i := by
  have hi (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : D.rationalLinear g (D.rationalLinear g⁻¹ u) = u := by
    rw [map_inv]
    exact LinearEquiv.apply_symm_apply _ _
  have h := g.property (D.rationalLinear g⁻¹ (Pi.single i 1)) (Pi.single j 1)
  change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian D.pel.reference.b
      (D.rationalLinear g (D.rationalLinear g⁻¹ (Pi.single i 1)))
      (D.rationalLinear g (Pi.single j 1)) =
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian D.pel.reference.b (D.rationalLinear g⁻¹ (Pi.single i 1)) (Pi.single j 1) at h
  rw [hi] at h
  change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian D.pel.reference.b (Pi.single i 1) (g.val.val.mulVec (Pi.single j 1)) =
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian D.pel.reference.b ((g⁻¹).val.val.mulVec (Pi.single i 1)) (Pi.single j 1) at h
  simpa [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, Matrix.mulVec_single, Pi.single_apply, apply_ite] using h

theorem Data.ActiveHeckeThetaData.localMatrix_opposite_entry (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (g : D.RationalSU)
    (v : Fin s × Bool) (i j : Fin 3) :
    (if i = 2 then D.localEmbedding v D.pel.reference.b else 1) *
      (D.localMatrix (v.1, !v.2) g).val i j =
    (if j = 2 then D.localEmbedding v D.pel.reference.b else 1) *
      (D.localMatrix v g⁻¹).val j i := by
  have h := congrArg (D.localEmbedding v) (D.rationalUnitary_opposite_entry g i j)
  rw [map_mul, map_mul, ← D.localEmbedding_conjugate hc hgood] at h
  change (if i = 2 then D.localEmbedding v D.pel.reference.b else 1) *
      D.localEmbedding (v.1, !v.2) (g.val.val i j) =
    (if j = 2 then D.localEmbedding v D.pel.reference.b else 1) *
      D.localEmbedding v ((g⁻¹).val.val j i)
  simpa only [apply_ite, map_one] using h

theorem Data.ActiveHeckeThetaData.localMatrix_opposite_integral (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (g : D.RationalSU) (v : Fin s × Bool)
    (hv : D.localMatrix v g ∈ SphericalGU.Spherical.integralSL3 q) :
    D.localMatrix (v.1, !v.2) g ∈ SphericalGU.Spherical.integralSL3 q := by
  apply (AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport.integralSL3_iff_entries q _).mpr
  intro i j
  have hu (k : Fin 3) : ‖(if k = 2 then D.localEmbedding v D.pel.reference.b else 1)‖ = 1 := by
    split_ifs
    · exact D.localEmbedding_b_norm hg hc hgood hdegree v
    · exact norm_one
  have he := congrArg (fun a : ℚ_[q] => ‖a‖) (D.localMatrix_opposite_entry hc hgood g v i j)
  rw [norm_mul, norm_mul, hu, hu, one_mul, one_mul] at he
  rw [he]
  apply (AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport.integralSL3_iff_entries q _).mp
  rw [map_inv]
  exact (SphericalGU.Spherical.integralSL3 q).inv_mem hv

end

end OAI.RepresentationTheory.Theta.Geometric

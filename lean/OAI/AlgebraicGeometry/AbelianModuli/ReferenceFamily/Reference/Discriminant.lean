import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Lattice
import OAI.RepresentationTheory.Theta.Geometric.IntegralDualLattice

/-! # Discriminant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual reference period lattice and its integral dual have the
specified doubled elementary divisors. The comparison retains the exact
integral form and constructs the finite discriminant group. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

def Fiber.ReferenceAnalyticFiber.integralLatticeEquiv : P.lattice ≃ₗ[ℤ] F.periodData.periodIntegerLattice :=
  F.latticeEquiv.toIntLinearEquiv

theorem Fiber.ReferenceAnalyticFiber.lattice_rank : Module.finrank ℤ F.periodData.periodIntegerLattice = 2 * (3 * s) := by
  rw [ZLattice.rank ℝ F.periodData.periodIntegerLattice]
  change Module.finrank ℝ (Fin (3 * Fintype.card (Fin s)) → ℂ) = _
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

def Fiber.ReferenceAnalyticFiber.latticeBasis : Module.Basis (Fin (2 * (3 * s))) ℤ F.periodData.periodIntegerLattice := by
  let L := F.periodData.periodIntegerLattice
  let : Module.Free ℤ L := ZLattice.module_free ℝ L
  let : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  exact (Module.finBasis ℤ L).reindex (finCongr F.lattice_rank)

def Fiber.ReferenceAnalyticFiber.dualLattice : Submodule ℤ (Fiber.ReferenceTangent s) :=
  LinearMap.BilinForm.dualSubmodule F.imaginaryForm F.periodData.periodIntegerLattice

instance Fiber.ReferenceAnalyticFiber.dualLattice_discrete : DiscreteTopology F.dualLattice :=
  RepresentationTheory.Theta.Geometric.IntegralDualLattice.dualLattice_discrete _ F.latticeBasis _ F.imaginaryForm_nondegenerate

instance Fiber.ReferenceAnalyticFiber.dualLattice_full : IsZLattice ℝ F.dualLattice :=
  RepresentationTheory.Theta.Geometric.IntegralDualLattice.dualLattice_full _ F.latticeBasis _ F.imaginaryForm_nondegenerate

def Fiber.ReferenceAnalyticFiber.dualLatticeEquiv : F.dualLattice ≃ₗ[ℤ] (F.periodData.periodIntegerLattice →ₗ[ℤ] ℤ) :=
  RepresentationTheory.Theta.Geometric.IntegralDualLattice.integralDualLatticeEquiv _ F.latticeBasis _ F.imaginaryForm_nondegenerate

def Fiber.ReferenceAnalyticFiber.dualReferenceEquiv : F.dualLattice ≃ₗ[ℤ] (P.lattice →ₗ[ℤ] ℤ) :=
  F.dualLatticeEquiv.trans F.integralLatticeEquiv.dualMap

theorem Fiber.ReferenceAnalyticFiber.lattice_le_dual (hP : P.IsAdmissible) : F.periodData.periodIntegerLattice ≤ F.dualLattice := by
  intro u hu v hv
  obtain ⟨a, ha⟩ := F.integralLatticeEquiv.surjective ⟨u, hu⟩
  obtain ⟨b, hb⟩ := F.integralLatticeEquiv.surjective ⟨v, hv⟩
  have he := F.latticeEquiv_polarization hP a b
  change F.imaginaryForm (F.integralLatticeEquiv a).val (F.integralLatticeEquiv b).val =
    (P.integralForm a b : ℝ) at he
  rw [ha, hb] at he
  exact Submodule.mem_one.mpr ⟨P.integralForm a b, he.symm⟩

def Fiber.ReferenceAnalyticFiber.latticeDualInclusion (hP : P.IsAdmissible) : P.lattice →ₗ[ℤ] F.dualLattice where
  toFun u := ⟨(F.integralLatticeEquiv u).val,
    F.lattice_le_dual hP (F.integralLatticeEquiv u).property⟩
  map_add' u v := Subtype.ext (congrArg
    (fun w : F.periodData.periodIntegerLattice => w.val) (map_add F.integralLatticeEquiv u v))
  map_smul' n u := Subtype.ext (congrArg
    (fun w : F.periodData.periodIntegerLattice => w.val) (map_smul F.integralLatticeEquiv n u))

theorem Fiber.ReferenceAnalyticFiber.dualReferenceEquiv_inclusion (hP : P.IsAdmissible) (u : P.lattice) :
    F.dualReferenceEquiv (F.latticeDualInclusion hP u) = P.integralForm u := by
  ext v
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ)
    (LinearMap.BilinForm.dualSubmoduleParing F.imaginaryForm
      (F.latticeDualInclusion hP u) (F.integralLatticeEquiv v)) = _
  exact (LinearMap.BilinForm.dualSubmoduleParing_spec F.imaginaryForm
    (F.latticeDualInclusion hP u) (F.integralLatticeEquiv v)).trans
      (F.latticeEquiv_polarization hP u v)

def Fiber.ReferenceAnalyticFiber.discriminantEquiv (hP : P.IsAdmissible) :
    (F.dualLattice ⧸ (F.latticeDualInclusion hP).range) ≃ₗ[ℤ]
      ((P.lattice →ₗ[ℤ] ℤ) ⧸ P.integralForm.range) :=
  Submodule.Quotient.equiv _ _ F.dualReferenceEquiv (by
    rw [← LinearMap.range_comp]
    congr 1
    ext u v
    exact LinearMap.congr_fun (F.dualReferenceEquiv_inclusion hP u) v)

theorem Fiber.ReferenceAnalyticFiber.discriminant_type (hP : P.IsAdmissible) :
    Nonempty ((F.dualLattice ⧸ (F.latticeDualInclusion hP).range) ≃+
      ((∀ i : Fin (3 * s), ZMod (P.polarizationType i)) ×
        (∀ i : Fin (3 * s), ZMod (P.polarizationType i)))) := by
  have h := hP
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _⟩
  exact ⟨(F.discriminantEquiv hP).toAddEquiv.trans ht.some⟩

theorem Fiber.ReferenceAnalyticFiber.discriminant_finite (hP : P.IsAdmissible) :
    Finite (F.dualLattice ⧸ (F.latticeDualInclusion hP).range) := by
  have h := hP
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
  let (i : Fin (3 * s)) : NeZero (P.polarizationType i) := ⟨ne_of_gt (hpos i)⟩
  exact Finite.of_equiv _ (F.discriminant_type hP).some.toEquiv.symm

theorem Fiber.ReferenceAnalyticFiber.dualLattice_bounded_denominator (hP : P.IsAdmissible) :
    ∃ n : ℕ, 0 < n ∧ ∀ v : F.dualLattice, n • v.val ∈ F.periodData.periodIntegerLattice := by
  let Q := F.dualLattice ⧸ (F.latticeDualInclusion hP).range
  let := F.discriminant_finite hP
  refine ⟨Nat.card Q, Nat.card_pos, ?_⟩
  intro v
  have hz : (Submodule.Quotient.mk (Nat.card Q • v) : Q) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact card_nsmul_eq_zero'
  obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hv := congrArg Subtype.val hu
  change (F.integralLatticeEquiv u).val = Nat.card Q • v.val at hv
  exact hv ▸ (F.integralLatticeEquiv u).property

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

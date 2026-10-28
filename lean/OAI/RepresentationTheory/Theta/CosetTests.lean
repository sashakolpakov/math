import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
import OAI.RepresentationTheory.Theta.Convergence

/-! # Coset Tests -/

namespace OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction

noncomputable section

/-! Lattice cosets as actual finite test functions and linearity of pure tensors. -/

open scoped Classical

variable {ι : Type*} [Fintype ι]

def latticeTestFunction (q : ℚ) (hq : q ≠ 0) : PoissonAutomorphyNormalizationData.finiteSchwartz ι := by
  refine ⟨PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq, (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr ⟨?_, ?_⟩⟩
  · exact ((LocallyConstant.const (ι → PoissonAutomorphyNormalizationData.AQf) (1 : ℂ)).indicator
      ⟨(PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact q hq).isClosed, PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen q hq⟩).isLocallyConstant
  · apply (PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact q hq).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact q hq).isClosed
    exact Set.support_indicator_subset

def latticeCosetTest (q : ℚ) (hq : q ≠ 0) (a : ι → PoissonAutomorphyNormalizationData.AQf) : PoissonAutomorphyNormalizationData.finiteSchwartz ι := by
  refine ⟨PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq a, (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr ⟨?_, ?_⟩⟩
  · exact ((PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp (latticeTestFunction q hq).property).1.comp_continuous
      (continuous_id.sub continuous_const)
  · have heq : PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq a =
        (latticeTestFunction q hq).val ∘ Homeomorph.addRight (-a) := by
      funext x
      change PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (x - a) = PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (x + -a)
      rw [sub_eq_add_neg]
    rw [heq]
    exact (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport (latticeTestFunction q hq)).comp_homeomorph _

theorem latticeCosetTest_apply (q : ℚ) (hq : q ≠ 0) (a x : ι → PoissonAutomorphyNormalizationData.AQf) :
    (latticeCosetTest q hq a).val x = PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq a x := rfl

def tensorLeft (f : PoissonAutomorphyNormalizationData.realSchwartz ι) : PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] PoissonAutomorphyNormalizationData.adelicSchwartz ι where
  toFun := PoissonAutomorphyNormalizationData.tensor f
  map_add' φ ψ := by
    apply Subtype.ext
    funext x
    change f.val _ * (φ.val _ + ψ.val _) = f.val _ * φ.val _ + f.val _ * ψ.val _
    ring
  map_smul' c φ := by
    apply Subtype.ext
    funext x
    change f.val _ * (c * φ.val _) = c * (f.val _ * φ.val _)
    ring

def tensorRight (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) : PoissonAutomorphyNormalizationData.realSchwartz ι →ₗ[ℂ] PoissonAutomorphyNormalizationData.adelicSchwartz ι where
  toFun f := PoissonAutomorphyNormalizationData.tensor f φ
  map_add' f g := by
    apply Subtype.ext
    funext x
    change (f.val _ + g.val _) * φ.val _ = f.val _ * φ.val _ + g.val _ * φ.val _
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change (c * f.val _) * φ.val _ = c * (f.val _ * φ.val _)
    ring

theorem finiteSchwartz_coset_expansion_eq (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ s : Finset (PoissonAutomorphyFiniteFourier.Construction.FiniteQuotient (ι := ι) (n : ℚ) (by exact_mod_cast hn.ne')),
      φ = ∑ c ∈ s, φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal (PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep (n : ℚ) (by exact_mod_cast hn.ne') c)) •
        latticeCosetTest (n : ℚ) (by exact_mod_cast hn.ne')
          (PoissonAutomorphyNormalizationData.finiteDiagonal (PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep (n : ℚ) (by exact_mod_cast hn.ne') c)) := by
  obtain ⟨n, hn, hp⟩ := PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_lattice_period φ
  obtain ⟨s, hs⟩ := PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_coset_expansion φ (n : ℚ) (by exact_mod_cast hn.ne') hp
  refine ⟨n, hn, s, ?_⟩
  apply Subtype.ext
  funext x
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, latticeCosetTest_apply] using hs x

end

end OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction

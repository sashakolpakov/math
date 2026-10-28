import OAI.RepresentationTheory.Theta.Adelic.Evaluation
import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies

/-! # Intrinsic -/

namespace OAI.RepresentationTheory.Theta.Intrinsic.OneFormsIntrinsic

noncomputable section

/-! Actual restricted-tensor Schwartz inputs for finite adelic lattice cosets. -/

open scoped _root_.NumberField Classical
open Filter

open OAI.RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies.Construction
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def cosetInput (q : F) (hq : q ≠ 0) (a : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    Adelic.FiniteSchwartz.finiteSchwartz F N :=
  Adelic.TensorProjective.Restricted.pure (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest F N q hq a)
    (Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest_eventually_vacuum F N q hq a)

theorem cosetInput_value (q : F) (hq : q ≠ 0)
    (a x : Fin N → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    Adelic.Evaluation.finiteSchwartzFunction F N (cosetInput F N q hq a) x =
      Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator q hq a x := by
  rw [cosetInput, Adelic.Evaluation.finiteSchwartzFunction_pure]
  rw [Weil.AdelicSplitting.FiniteLatticeFactors.Construction.finitePositionCosetIndicator_product]
  symm
  apply tprod_eq_finprod
  exact eventually_cofinite.mp
    (by
      have hf := Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest_eventually_vacuum F N q hq a
      have hx := Adelic.Evaluation.vacuum_evaluation_eventually_one F N x
      filter_upwards [hf, hx] with v hv hval
      change (Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest F N q hq a v).val (fun i => x i v) = 1
      rw [hv]
      exact hval)

theorem cosetInput_rational_value (q : F) (hq : q ≠ 0)
    (a x : Fin N → F) :
    Adelic.Evaluation.finiteSchwartzFunction F N
        (cosetInput F N q hq (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a))
        (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      if ∃ r : Fin N → 𝓞 F, x = a + q • (fun i => (r i : F))
      then 1 else 0 := by
  rw [cosetInput_value]
  have hmem : Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a ∈
      Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice q hq ↔
        ∃ r : Fin N → 𝓞 F, x = a + q • (fun i => (r i : F)) := by
    have he : Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a =
        Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (x - a) := by
      funext i
      exact (map_sub (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) (x i) (a i)).symm
    rw [he]
    change (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ((x - a) i)) ∈
      Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice q hq ↔ _
    rw [Weil.AdelicSplitting.FiniteLattices.Construction.rational_mem_finiteAdelicPositionLattice_iff]
    constructor
    · intro h
      choose r hr using h
      refine ⟨r, ?_⟩
      ext i
      exact (sub_eq_iff_eq_add.mp (hr i).symm).trans (add_comm _ _)
    · rintro ⟨r, rfl⟩ i
      exact ⟨r i, by simp⟩
  simp only [Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator, Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionIndicator,
    Set.indicator_apply, SetLike.mem_coe, hmem]

end

end OAI.RepresentationTheory.Theta.Intrinsic.OneFormsIntrinsic

import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets
import OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum
import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterScaling
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCosetFourier

/-! # Finite Lattice Factors -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLatticeFactors.Construction

noncomputable section

/-! Scalar lattices and their cosets in finite adelic position space
factor into the actual compact open lattices at finite places. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def finiteLocalIntegralPositions (v : HeightOneSpectrum (𝓞 F)) :
    OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :=
  ⟨{ carrier := {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
     zero_mem' := fun _ => (v.adicCompletionIntegers F).zero_mem
     add_mem' := fun hx hy i => (v.adicCompletionIntegers F).toSubring.add_mem (hx i) (hy i)
     neg_mem' := fun hx i => (v.adicCompletionIntegers F).toSubring.neg_mem (hx i) },
   by simpa only [Vacuum.Construction.finitePositionLattice, Set.mem_univ, forall_const, Set.pi] using!
      (Vacuum.Construction.finitePositionLattice_clopen F N v).isOpen⟩

theorem finiteLocalIntegralPositions_compact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (finiteLocalIntegralPositions F N v : Set (Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N)) := by
  simpa only [Vacuum.Construction.finitePositionLattice, Set.mem_univ, forall_const, Set.pi] using!
    (Vacuum.Construction.finitePositionLattice_compact F N v)

def finiteLocalScalarLattice (q : F) (hq : q ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :=
  let e := CharacterScaling.LocalAnalysis.scalarPositionEquiv N (ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q)
    ((ArchimedeanAdeles.Construction.rationalScalar F (.inr v)).injective.ne (by simpa using hq))
  (finiteLocalIntegralPositions F N v).comap e.symm.toLinearMap.toAddMonoidHom e.symm.continuous

theorem finiteLocalScalarLattice_mem_iff (q : F) (hq : q ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :
    x ∈ finiteLocalScalarLattice F N q hq v ↔
      ∀ i, (ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q)⁻¹ * x i ∈ v.adicCompletionIntegers F := Iff.rfl

theorem finiteLocalScalarLattice_compact (q : F) (hq : q ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (finiteLocalScalarLattice F N q hq v : Set (Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) N)) := by
  let e := CharacterScaling.LocalAnalysis.scalarPositionEquiv N (ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q)
    ((ArchimedeanAdeles.Construction.rationalScalar F (.inr v)).injective.ne (by simpa using hq))
  exact e.symm.toHomeomorph.isCompact_preimage.mpr (finiteLocalIntegralPositions_compact F N v)

theorem finiteAdelicPositionLattice_local_iff (q : F) (hq : q ≠ 0) (x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    x ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq ↔
      ∀ v : HeightOneSpectrum (𝓞 F), (fun i => x i v) ∈ finiteLocalScalarLattice F N q hq v := by
  rw [FiniteLattices.Construction.finiteAdelicPositionLattice_mem_iff]
  simp only [finiteLocalScalarLattice_mem_iff]
  change (∀ i v, ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q⁻¹ * x i v ∈ v.adicCompletionIntegers F) ↔ _
  simp only [map_inv₀]
  exact forall_comm

theorem finitePositionCosetIndicator_product (q : F) (hq : q ≠ 0)
    (a x : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    FiniteCosets.Construction.finitePositionCosetIndicator q hq a x =
      ∏' v : HeightOneSpectrum (𝓞 F),
        LocalCosetFourier.Analysis.localCosetIndicator (finiteLocalScalarLattice F N q hq v) (fun i => a i v) (fun i => x i v) := by
  by_cases hx : x - a ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq
  · have hlocal := (finiteAdelicPositionLattice_local_iff F N q hq (x - a)).mp hx
    have hprod : (fun v : HeightOneSpectrum (𝓞 F) =>
        LocalCosetFourier.Analysis.localCosetIndicator (finiteLocalScalarLattice F N q hq v) (fun i => a i v) (fun i => x i v)) =
        fun _ => (1 : ℂ) := by
      funext v
      exact Set.indicator_of_mem (hlocal v) _
    rw [hprod, tprod_one]
    change (FiniteLattices.Construction.finiteAdelicPositionLattice (ι := Fin N) q hq : Set (Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F)).indicator
      (fun _ => (1 : ℂ)) (x - a) = 1
    exact Set.indicator_of_mem hx _
  · have hnot : ¬ ∀ v : HeightOneSpectrum (𝓞 F),
        (fun i => (x - a) i v) ∈ finiteLocalScalarLattice F N q hq v := by
      exact fun h => hx ((finiteAdelicPositionLattice_local_iff F N q hq (x - a)).mpr h)
    push Not at hnot
    obtain ⟨v, hv⟩ := hnot
    rw [tprod_of_exists_eq_zero ⟨v, Set.indicator_of_notMem hv _⟩]
    change (FiniteLattices.Construction.finiteAdelicPositionLattice (ι := Fin N) q hq : Set (Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F)).indicator
      (fun _ => (1 : ℂ)) (x - a) = 0
    exact Set.indicator_of_notMem hx _

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLatticeFactors.Construction

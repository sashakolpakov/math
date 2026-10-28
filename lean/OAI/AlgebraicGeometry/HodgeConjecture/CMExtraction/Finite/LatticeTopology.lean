import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLattices
import OAI.RepresentationTheory.Theta.Adelic.CompactOpen

/-! # Lattice Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.LatticeTopology.TestTransport

noncomputable section

/-! Integer multiples of the integral position lattice form a basis of
zero-neighborhoods in the actual finite adeles of a number field. -/

open scoped Classical _root_.NumberField RestrictedProduct _root_.Topology
open OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction IsDedekindDomain

theorem open_add_subgroup_inside_nhds_zero {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (U : Set G) (hU : U ∈ 𝓝 (0 : G)) :
    ∃ V : OpenAddSubgroup G, (V : Set G) ⊆ U := by
  let : T2Space (Multiplicative G) := inferInstanceAs (T2Space G)
  let : TotallyDisconnectedSpace (Multiplicative G) :=
    inferInstanceAs (TotallyDisconnectedSpace G)
  obtain ⟨K, _, hK⟩ := RepresentationTheory.Theta.Adelic.CompactOpen.compact_open_subgroup_basis
    (G := Multiplicative G) U hU
  let V : OpenAddSubgroup G :=
    { carrier := K.toSubgroup.carrier
      zero_mem' := K.one_mem
      add_mem' := K.mul_mem
      neg_mem' := K.inv_mem
      isOpen' := K.isOpen }
  exact ⟨V, hK⟩

variable (F : Type) [Field F] [NumberField F]

theorem finiteAdeles_locallyCompact : LocallyCompactSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) := by
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v => Valued.isOpen_valuationSubring (v.adicCompletion F)⟩
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem finiteAdeles_t2 : T2Space (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem finiteAdeles_totallyDisconnected : TotallyDisconnectedSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) := by
  have hc : Continuous (fun x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => fun v => x v) :=
    continuous_pi (fun v => RestrictedProduct.continuous_eval v)
  exact ⟨isTotallyDisconnected_of_image hc.continuousOn DFunLike.coe_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem finitePosition_integer_lattice_nhds {I : Type*} [Fintype I]
    (U : Set (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) (hU : U ∈ 𝓝 (0 : I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) :
    ∃ N : ℕ, ∃ hN : 0 < N,
      (RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (ι := I) (N : F) (by exact_mod_cast hN.ne') :
        Set (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) ⊆ U := by
  let := finiteAdeles_locallyCompact F
  let := finiteAdeles_t2 F
  let := finiteAdeles_totallyDisconnected F
  obtain ⟨V, hVU⟩ := open_add_subgroup_inside_nhds_zero U hU
  obtain ⟨N, hN, hsmall⟩ := RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finitePosition_open_integer_multiple F V
  refine ⟨N, hN, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  apply hVU
  change RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finitePositionScale (N : F) y ∈ V
  rw [RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finitePositionScale_natCast]
  exact hsmall (fun i => ⟨y i, hy i⟩)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.LatticeTopology.TestTransport

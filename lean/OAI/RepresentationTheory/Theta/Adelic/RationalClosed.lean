import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness
import OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection

/-! # Rational Closed -/

namespace OAI.RepresentationTheory.Theta.Adelic.RationalClosed

noncomputable section

/-! Closedness of the actual rational additive diagonal, in base and
quadratic adelic coordinates. -/

open scoped _root_.NumberField _root_.Topology

open OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness.Construction

variable (F : Type) [Field F] [NumberField F]

instance adelesNontrivial : Nontrivial (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) :=
  inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing F × Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))

instance finiteAdelesLocallyCompact : LocallyCompactSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  (Weil.AdelicSplitting.IntegralAdeles.Construction.isCompact_finiteIntegralRing F).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Weil.AdelicSplitting.IntegralAdeles.Construction.isOpen_finiteIntegralRing F).mem_nhds (Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F).zero_mem)

instance adelesLocallyCompact : LocallyCompactSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) := by
  let : LocallyCompactSpace (NumberField.InfiniteAdeleRing F) :=
    (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).isClosedEmbedding.locallyCompactSpace
  exact inferInstanceAs (LocallyCompactSpace (NumberField.InfiniteAdeleRing F × Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))

instance adelesT2 : T2Space (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) := by
  let : T2Space (NumberField.InfiniteAdeleRing F) :=
    (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).symm.t2Space
  let : T2Space (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) := inferInstanceAs (T2Space (RestrictedProduct
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  exact inferInstanceAs (T2Space (NumberField.InfiniteAdeleRing F × Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))

theorem rational_range_closed : IsClosed (Set.range (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F))) := by
  let : TopologicalSpace F := ⊥
  let : DiscreteTopology F := discreteTopology_bot F
  have hp : IsProperMap (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)) := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨continuous_of_discreteTopology, ?_⟩
    intro K hK
    exact (Weil.AdelicSplitting.RationalDiscreteness.Construction.finite_rational_preimage_compact F K hK).isCompact
  exact hp.isClosed_range

theorem quadraticRational_range_closed (d : F) :
    IsClosed (Set.range (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticRational F d)) := by
  have he : Set.range (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticRational F d) =
      {z : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d | z.re ∈ Set.range (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)) ∧
        z.im ∈ Set.range (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F))} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.re, rfl⟩, ⟨a.im, rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨⟨a, b⟩, QuadraticAlgebra.ext ha hb⟩
  rw [he]
  exact ((rational_range_closed F).preimage (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re _)).inter
    ((rational_range_closed F).preimage (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im _))

end

end OAI.RepresentationTheory.Theta.Adelic.RationalClosed

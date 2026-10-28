import OAI.RepresentationTheory.Theta.Adelic.IdeleClassClosed
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient

/-! # Idele Class Embedding -/

namespace OAI.RepresentationTheory.Theta.Adelic.IdeleClassEmbedding

noncomputable section

/-! The base idele-class map is a closed topological embedding. The
open-mapping step uses a countable compact covering of the actual adele
ring, obtained from its rational translates of compact representatives. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection
open OAI.RepresentationTheory.Theta.Adelic.IdeleClassClosed OAI.RepresentationTheory.Theta.Adelic.RationalClosed

variable (F : Type) [Field F] [NumberField F]

instance adelesSigmaCompact : SigmaCompactSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) := by
  let : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  let K : F → Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) := fun q =>
    (fun x => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q + x) '' Weil.AdelicSplitting.CompactQuotient.Construction.adelicCompactRepresentatives F
  have hK : ∀ q, IsCompact (K q) := fun q =>
    (Weil.AdelicSplitting.CompactQuotient.Construction.isCompact_adelicCompactRepresentatives F).image (continuous_const.add continuous_id)
  have hcover : (⋃ q, K q) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    obtain ⟨q, hq⟩ := Weil.AdelicSplitting.CompactQuotient.Construction.rational_translates_cover_adeles F a
    exact Set.mem_iUnion.mpr ⟨q, a - algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q, hq, add_sub_cancel _ _⟩
  apply isSigmaCompact_univ_iff.mp
  rw [← hcover]
  exact isSigmaCompact_iUnion_of_isCompact K hK

instance idelesSigmaCompact : SigmaCompactSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ := by
  let : SigmaCompactSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

instance ideleClassSigmaCompact : SigmaCompactSpace (NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass F) := by
  apply isSigmaCompact_univ_iff.mp
  have h := isSigmaCompact_range (QuotientGroup.continuous_mk
    (N := (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range))
  simpa only [Set.range_eq_univ.mpr QuotientGroup.mk_surjective] using h

variable (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)

include hns in
theorem quadraticPrincipal_range_closed :
    IsClosed ((IdeleClassInjection.quadraticPrincipal F d).range : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) := by
  have he : ((IdeleClassInjection.quadraticPrincipal F d).range : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) =
      Units.val ⁻¹' Set.range (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticRational F d) := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.val, rfl⟩
    · rintro ⟨b, hb⟩
      let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := ⟨by
        intro r hr
        apply hns
        exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using hr.symm⟩⟩
      have hb0 : b ≠ 0 := by
        intro h
        exact a.ne_zero (hb.symm.trans (h ▸ map_zero _))
      exact ⟨Units.mk0 b hb0, Units.ext hb⟩
  rw [he]
  exact (RationalClosed.quadraticRational_range_closed F d).preimage Units.continuous_val

include hd hns in
theorem scalarIdeleClass_closedEmbedding : Topology.IsClosedEmbedding (IdeleClassInjection.scalarIdeleClass F d) := by
  let : IsClosed ((IdeleClassInjection.quadraticPrincipal F d).range : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :=
    quadraticPrincipal_range_closed F d hns
  let : T2Space (IdeleClassInjection.QuadraticIdeleClass F d) := inferInstance
  let : LocallyCompactSpace (IdeleClassInjection.QuadraticIdeleClass F d) := inferInstance
  let : LocallyCompactSpace (IdeleClassInjection.scalarIdeleClass F d).range :=
    (IdeleClassClosed.scalarIdeleClass_range_closed F d hd hns).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let f := (IdeleClassInjection.scalarIdeleClass F d).rangeRestrict
  have hc : Continuous f := (IdeleClassInjection.scalarIdeleClass_continuous F d).subtype_mk _
  have hs : Function.Surjective f := by
    rintro ⟨y, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  have hi : Function.Injective f := fun x y h =>
    IdeleClassInjection.scalarIdeleClass_injective F d (congrArg Subtype.val h)
  have ho : IsOpenMap f := f.isOpenMap_of_sigmaCompact hs hc
  exact ⟨Topology.IsEmbedding.subtypeVal.comp
      (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi ho).isEmbedding,
    IdeleClassClosed.scalarIdeleClass_range_closed F d hd hns⟩

end

end OAI.RepresentationTheory.Theta.Adelic.IdeleClassEmbedding

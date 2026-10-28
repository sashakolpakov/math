import OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Compact Quotient -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction

noncomputable section

/-! A compact set of representatives for the actual additive adelic quotient
by the number field. This uses finite strong approximation and the integral
Minkowski lattice, with no operator-relation assumption. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem exists_rational_finite_integral_remainder (a : ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∃ q : F, a - algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) q ∈ IntegralAdeles.Construction.finiteIntegralRing F := by
  let U : Set (ArchimedeanAdeles.Construction.FiniteAdeles F) := {b | a - b ∈ IntegralAdeles.Construction.finiteIntegralRing F}
  have hU : IsOpen U := (IntegralAdeles.Construction.isOpen_finiteIntegralRing F).preimage
    (continuous_const.sub continuous_id)
  have ha : a ∈ U := by change a - a ∈ IntegralAdeles.Construction.finiteIntegralRing F; rw [sub_self]; exact zero_mem _
  exact (StrongApproximation.Construction.denseRange_rational_finiteAdeles F).exists_mem_open hU ⟨a, ha⟩

theorem exists_integer_mixed_remainder (x : mixedEmbedding.mixedSpace F) :
    ∃ r : 𝓞 F, x - mixedEmbedding F (algebraMap (𝓞 F) F r) ∈
      parallelepiped (mixedEmbedding.latticeBasis F) := by
  let b := mixedEmbedding.latticeBasis F
  have hmem : (ZSpan.floor b x).val ∈ mixedEmbedding.integerLattice F := by
    rw [← mixedEmbedding.span_latticeBasis F]
    exact (ZSpan.floor b x).property
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  change mixedEmbedding F (algebraMap (𝓞 F) F r) = (ZSpan.floor b x).val at hr
  rw [hr]
  exact (ZSpan.fundamentalDomain_subset_parallelepiped b) (ZSpan.fract_mem_fundamentalDomain b x)

def adelicMixedHomeomorph :
    ArchimedeanAdeles.Construction.Adeles F ≃ₜ mixedEmbedding.mixedSpace F × ArchimedeanAdeles.Construction.FiniteAdeles F :=
  (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).prodCongr (Homeomorph.refl (ArchimedeanAdeles.Construction.FiniteAdeles F))

def adelicCompactRepresentatives : Set (ArchimedeanAdeles.Construction.Adeles F) :=
  (adelicMixedHomeomorph F).symm ''
    (parallelepiped (mixedEmbedding.latticeBasis F) ×ˢ (IntegralAdeles.Construction.finiteIntegralRing F : Set (ArchimedeanAdeles.Construction.FiniteAdeles F)))

theorem isCompact_adelicCompactRepresentatives : IsCompact (adelicCompactRepresentatives F) := by
  apply IsCompact.image _ (adelicMixedHomeomorph F).symm.continuous
  exact (mixedEmbedding.latticeBasis F).parallelepiped.isCompact.prod (IntegralAdeles.Construction.isCompact_finiteIntegralRing F)

theorem mem_adelicCompactRepresentatives (a : ArchimedeanAdeles.Construction.Adeles F) :
    a ∈ adelicCompactRepresentatives F ↔
      ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F a.1 ∈ parallelepiped (mixedEmbedding.latticeBasis F) ∧
      a.2 ∈ IntegralAdeles.Construction.finiteIntegralRing F := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    change ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F ((ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).symm b.1) ∈ _ ∧ b.2 ∈ _
    rw [(ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).apply_symm_apply]
    exact hb
  · intro ha
    exact ⟨adelicMixedHomeomorph F a, ha, (adelicMixedHomeomorph F).symm_apply_apply a⟩

theorem rational_translates_cover_adeles (a : ArchimedeanAdeles.Construction.Adeles F) :
    ∃ q : F, a - algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q ∈ adelicCompactRepresentatives F := by
  obtain ⟨q, hq⟩ := exists_rational_finite_integral_remainder F a.2
  obtain ⟨r, hr⟩ := exists_integer_mixed_remainder F
    (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F (a - algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q).1)
  refine ⟨q + algebraMap (𝓞 F) F r, (mem_adelicCompactRepresentatives F _).mpr ⟨?_, ?_⟩⟩
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F
      (a.1 - algebraMap F (InfiniteAdeleRing F) (q + algebraMap (𝓞 F) F r)) ∈ _
    change InfiniteAdeleRing.ringEquiv_mixedSpace F
      (a.1 - algebraMap F (InfiniteAdeleRing F) q) - mixedEmbedding F (algebraMap (𝓞 F) F r) ∈ _ at hr
    rw [map_add, sub_add_eq_sub_sub, map_sub,
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    exact hr
  · have hh := (IntegralAdeles.Construction.finiteIntegralRing F).sub_mem hq (IntegralAdeles.Construction.algebraMap_mem_finiteIntegralRing F r)
    simpa only [map_add, Prod.snd_sub, Prod.snd_add, sub_add_eq_sub_sub,
      IsScalarTower.algebraMap_apply] using! hh

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction

import OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Rational Discreteness -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness.Construction

noncomputable section

/-! Finiteness of rational points in compact adelic sets. Finite-place
supports clear denominators; the archimedean images then lie in an actual
Minkowski integer lattice. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem compact_finiteAdeles_common_denominator (K : Set (ArchimedeanAdeles.Construction.FiniteAdeles F)) (hK : IsCompact K) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ a ∈ K,
      algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) r * a ∈ IntegralAdeles.Construction.finiteIntegralRing F := by
  have hc : Continuous (fun a : ArchimedeanAdeles.Construction.FiniteAdeles F => fun _ : Unit => a) :=
    continuous_pi (fun _ => continuous_id)
  obtain ⟨r, hr, hKr⟩ := IntegralAdeles.Construction.compact_subset_finiteIntegralBox F _ (hK.image hc)
  exact ⟨r, hr, fun a ha => hKr (Set.mem_image_of_mem _ ha) ()⟩

theorem finite_rational_preimage_compact (K : Set (ArchimedeanAdeles.Construction.Adeles F)) (hK : IsCompact K) :
    Set.Finite {q : F | algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q ∈ K} := by
  obtain ⟨r, hr, hKr⟩ := compact_finiteAdeles_common_denominator F _
    (hK.image (continuous_snd : Continuous (fun a : ArchimedeanAdeles.Construction.Adeles F => a.2)))
  let rF := algebraMap (𝓞 F) F r
  have hrF : rF ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  let f : ArchimedeanAdeles.Construction.Adeles F → mixedEmbedding.mixedSpace F := fun a =>
    mixedEmbedding F rF * ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F a.1
  have hf : Continuous f := continuous_const.mul
    ((ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).continuous.comp continuous_fst)
  let T := f '' K
  have hT : IsCompact T := hK.image hf
  have hfinite : Set.Finite (T ∩ mixedEmbedding.integerLattice F) := by
    rw [← mixedEmbedding.span_latticeBasis F]
    exact ZSpan.setFinite_inter (mixedEmbedding.latticeBasis F) hT.isBounded
  let g : F → mixedEmbedding.mixedSpace F := fun q => mixedEmbedding F (rF * q)
  have hg : Function.Injective g := (mixedEmbedding_injective F).comp (mul_right_injective₀ hrF)
  apply Set.Finite.of_finite_image (f := g) _ (Set.injOn_of_injective hg)
  apply hfinite.subset
  rintro _ ⟨q, hq, rfl⟩
  constructor
  · refine ⟨algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q, hq, ?_⟩
    dsimp only [f, g]
    rw [map_mul, ← ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph_rational F q]
    rfl
  · have hqr : algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (rF * q) ∈ IntegralAdeles.Construction.finiteIntegralRing F := by
      have hh := hKr _ (Set.mem_image_of_mem Prod.snd hq)
      simpa only [map_mul, rF, ← IsScalarTower.algebraMap_apply] using! hh
    obtain ⟨b, hb⟩ := (IntegralAdeles.Construction.rational_mem_finiteIntegral_iff F (rF * q)).mp hqr
    change ∃ b : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F b) = g q
    exact ⟨b, congrArg (mixedEmbedding F) hb⟩

theorem finite_rational_positions_preimage_compact {ι : Type*} [Fintype ι]
    (K : Set (ι → ArchimedeanAdeles.Construction.Adeles F)) (hK : IsCompact K) :
    Set.Finite {q : ι → F | (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) ∈ K} := by
  let S : ι → Set F := fun i => {q | algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q ∈ (fun a : ι → ArchimedeanAdeles.Construction.Adeles F => a i) '' K}
  have hS : ∀ i, (S i).Finite := fun i =>
    finite_rational_preimage_compact F _ (hK.image (continuous_apply i))
  apply (Set.Finite.pi hS).subset
  intro q hq i _
  exact Set.mem_image_of_mem (fun a : ι → ArchimedeanAdeles.Construction.Adeles F => a i) hq

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness.Construction

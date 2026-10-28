import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Data
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Function Gluing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

noncomputable section

section

/-! The original holomorphic function sheaf glues literal compatible section values. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem exists_holomorphicFunction_glue {ι : Type} (U : ι → Opens M)
    (f : ∀ i, Exponential.HolomorphicFunction (E := E) (M := U i))
    (hc : ∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    ∃ g : Exponential.HolomorphicFunction (E := E) (M := ↥(⨆ i, U i)),
      ∀ i (x : U i), g ⟨x.val, (le_iSup U i) x.property⟩ = f i x := by
  let P : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of M) := (Holomorphic.Sheaves.holomorphicFunctionSheaf E M).obj
  have hcompat : P.IsCompatible U f := by
    intro i j
    apply ContMDiffMap.ext
    intro x
    exact hc i j x.val x.property.1 x.property.2
  have hP : P.IsSheaf := (Holomorphic.Sheaves.holomorphicFunctionSheaf E M).property
  obtain ⟨g, hg, _⟩ := ((TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing P).mp hP) U f hcompat
  refine ⟨g, ?_⟩
  intro i x
  exact congrArg (fun h : Exponential.HolomorphicFunction (E := E) (M := U i) => h x) (hg i)

end

/-! The actual compatible coordinates of holomorphic bundle sections satisfy sheaf gluing. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u : Connecting.holomorphicUnitCohomology E M)

theorem exists_holomorphicLineSection_glue {ι : Type} (U : ι → Opens M)
    (s : ∀ a, HolomorphicSection.Data.HolomorphicLineSection u (U a))
    (hc : ∀ a b, HolomorphicSection.Data.holomorphicLineSectionRestrict inf_le_left (s a) =
      HolomorphicSection.Data.holomorphicLineSectionRestrict inf_le_right (s b)) :
    ∃ g : HolomorphicSection.Data.HolomorphicLineSection u (⨆ a, U a),
      ∀ a, HolomorphicSection.Data.holomorphicLineSectionRestrict (le_iSup U a) g = s a := by
  have hlocal (i : M) := exists_holomorphicFunction_glue
    (fun a => U a ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) (fun a => (s a).val i) (by
      intro a b x ha hb
      exact congrArg (fun z : HolomorphicSection.Data.HolomorphicLineSection u (U a ⊓ U b) =>
        z.val i ⟨x, ⟨ha.1, hb.1⟩, ha.2⟩) (hc a b))
  choose f hf using hlocal
  have hsub (i : M) : (⨆ a, U a) ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i ≤
      ⨆ a, U a ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i := by rw [iSup_inf_eq]
  let g : HolomorphicSection.Data.holomorphicLineLocalSections u (⨆ a, U a) := fun i => HolomorphicSection.Data.holomorphicOpenRestriction (hsub i) (f i)
  have hg (i : M) (a : ι) (x : ↥(U a ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i)) :
      g i ⟨x.val, (le_iSup U a) x.property.1, x.property.2⟩ = (s a).val i x := hf i a x
  have hgc : g ∈ HolomorphicSection.Data.holomorphicLineSectionSubmodule u (⨆ a, U a) := by
    intro i j x hx hi hj
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
    rw [hg j a ⟨x, ha, hj⟩, hg i a ⟨x, ha, hi⟩]
    exact (s a).property i j x ha hi hj
  refine ⟨⟨g, hgc⟩, ?_⟩
  intro a
  apply HolomorphicSection.Data.holomorphicLineSection_ext
  intro i x
  exact hg i a x

theorem holomorphicLineSection_eq_of_restrictions {ι : Type} (U : ι → Opens M)
    (s t : HolomorphicSection.Data.HolomorphicLineSection u (⨆ a, U a))
    (h : ∀ a, HolomorphicSection.Data.holomorphicLineSectionRestrict (le_iSup U a) s = HolomorphicSection.Data.holomorphicLineSectionRestrict (le_iSup U a) t) : s = t := by
  apply HolomorphicSection.Data.holomorphicLineSection_ext
  intro i x
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp x.property.1
  exact congrArg (fun z : HolomorphicSection.Data.HolomorphicLineSection u (U a) => z.val i ⟨x.val, ha, x.property.2⟩) (h a)

def holomorphicLineSectionPresheaf : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of M) where
  obj U := ModuleCat.of ℂ (HolomorphicSection.Data.HolomorphicLineSection u U.unop)
  map i := ModuleCat.ofHom (HolomorphicSection.Data.holomorphicLineSectionRestrict (leOfHom i.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact HolomorphicSection.Data.holomorphicLineSectionRestrict_self s
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (HolomorphicSection.Data.holomorphicLineSectionRestrict_comp (leOfHom i.unop) (leOfHom j.unop) s).symm

theorem holomorphicLineSectionPresheaf_isSheaf : (holomorphicLineSectionPresheaf u).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (holomorphicLineSectionPresheaf u)).mpr
  intro ι U s hc
  obtain ⟨g, hg⟩ := exists_holomorphicLineSection_glue u U s hc
  refine ⟨g, hg, ?_⟩
  intro t ht
  exact holomorphicLineSection_eq_of_restrictions u U t g (fun a => (ht a).trans (hg a).symm)

def holomorphicLineSectionSheaf : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M) where
  obj := holomorphicLineSectionPresheaf u
  property := holomorphicLineSectionPresheaf_isSheaf u

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

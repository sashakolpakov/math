import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVectorChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap

/-! # Stalk Map -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions

/-! The actual global-section-to-stalk ring map, and exact invariance
of the native equation ideal under an elementary section-head change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVectorChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sectionStalkMap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B : V.carrier.Opens) (x : V.carrier) (hxB : x ∈ B) :
    Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤) →+* V.carrier.presheaf.stalk x :=
  (B.topIso.hom ≫ V.carrier.presheaf.germ B x hxB).hom

theorem sectionStalkMap_restrict (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B C : V.carrier.Opens) (hCB : C ≤ B)
    (x : V.carrier) (hxC : x ∈ C) (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    sectionStalkMap V C x hxC (BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB s) = sectionStalkMap V B x (hCB hxC) s :=
  BaseSectionVectorChange.Constructions.section_stalk_restrict V B C hCB x hxC s

theorem ofList_head_difference {R : Type*} [CommRing R] (a b : R) (rs : List R)
    (h : b - a ∈ Ideal.ofList rs) : Ideal.ofList (b :: rs) = Ideal.ofList (a :: rs) := by
  have he : a + (b - a) = b := by ring
  exact (congrArg (fun z => Ideal.ofList (z :: rs)) he).symm.trans (Regular.SequenceTailChange.Constructions.ofList_add_tail a (b - a) rs h)

theorem ofList_ofFn {R : Type*} [CommRing R] (n : ℕ) (s : Fin n → R) :
    Ideal.ofList (List.ofFn s) = Ideal.span (Set.range s) := by
  apply congrArg Ideal.span
  ext a
  exact List.mem_ofFn' s a

theorem section_head_ideal (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B C : V.carrier.Opens) (hCB : C ≤ B)
    (x : V.carrier) (hxC : x ∈ C) (n : ℕ)
    (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (a : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤))
    (ha : a - BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB r ∈ Ideal.span (Set.range (fun i => BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i)))) :
    Ideal.ofList (sectionStalkMap V C x hxC a :: List.ofFn (fun i => sectionStalkMap V B x (hCB hxC) (s i))) =
      Ideal.ofList (sectionStalkMap V B x (hCB hxC) r :: List.ofFn (fun i => sectionStalkMap V B x (hCB hxC) (s i))) := by
  let gC := sectionStalkMap V C x hxC
  let gB := sectionStalkMap V B x (hCB hxC)
  have he : (fun i => gC (BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))) = (fun i => gB (s i)) :=
    funext (fun i => sectionStalkMap_restrict V B C hCB x hxC (s i))
  have hI : (Ideal.span (Set.range (fun i => BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i)))).map gC =
      Ideal.ofList (List.ofFn (fun i => gB (s i))) := by
    rw [Ideal.map_span, ← Set.range_comp']
    change Ideal.span (Set.range (fun i => gC (BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i)))) = _
    rw [he]
    exact (ofList_ofFn n (fun i => gB (s i))).symm
  have hv : gC (a - BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB r) = gC a - gB r :=
    (map_sub gC a _).trans (congrArg (fun z => gC a - z) (sectionStalkMap_restrict V B C hCB x hxC r))
  have hm := Ideal.mem_map_of_mem gC ha
  have hmem : gC a - gB r ∈ Ideal.ofList (List.ofFn (fun i => gB (s i))) :=
    (congrArg₂ (fun (b : V.carrier.presheaf.stalk x) (I : Ideal (V.carrier.presheaf.stalk x)) => b ∈ I) hv hI).mp hm
  exact ofList_head_difference (gB r) (gC a) (List.ofFn (fun i => gB (s i))) hmem

end AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms

/-! Native stalk lists of actual section vectors and their restriction
identities, together with the corresponding analytic base inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def vectorGerms (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B : V.carrier.Opens) (x : V.carrier) (hxB : x ∈ B)
    (n : ℕ) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) : List (V.carrier.presheaf.stalk x) :=
  (List.ofFn s).map (sectionStalkMap V B x hxB)

theorem vectorGerms_length (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B : V.carrier.Opens)
    (x : V.carrier) (hxB : x ∈ B) (n : ℕ) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    (vectorGerms V B x hxB n s).length = n := by
  simp only [vectorGerms, List.length_map, List.length_ofFn]

theorem vectorGerms_cons (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B : V.carrier.Opens)
    (x : V.carrier) (hxB : x ∈ B) (n : ℕ) (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    vectorGerms V B x hxB (n + 1) (Fin.cons r s) =
      sectionStalkMap V B x hxB r :: vectorGerms V B x hxB n s := by
  simp only [vectorGerms, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.map_cons]

theorem vectorGerms_one (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B : V.carrier.Opens)
    (x : V.carrier) (hxB : x ∈ B) (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    vectorGerms V B x hxB 1 (fun _ => r) = [sectionStalkMap V B x hxB r] := by
  simp only [vectorGerms, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil]

theorem vectorGerms_restrict (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B C : V.carrier.Opens) (hCB : C ≤ B)
    (x : V.carrier) (hxC : x ∈ C) (n : ℕ) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    vectorGerms V C x hxC n (fun i => BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i)) =
      vectorGerms V B x (hCB hxC) n s := by
  simp only [vectorGerms, List.map_ofFn]
  exact congrArg List.ofFn (funext (fun i => sectionStalkMap_restrict V B C hCB x hxC (s i)))

theorem vectorGerms_head_ideal (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B C : V.carrier.Opens) (hCB : C ≤ B)
    (x : V.carrier) (hxC : x ∈ C) (n : ℕ) (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (a : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤))
    (ha : a - BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB r ∈ Ideal.span (Set.range (fun i => BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i)))) :
    Ideal.ofList (vectorGerms V C x hxC (n + 1) (Fin.cons a (fun i => BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i)))) =
      Ideal.ofList (vectorGerms V B x (hCB hxC) (n + 1) (Fin.cons r s)) := by
  rw [vectorGerms_cons, vectorGerms_cons, vectorGerms_restrict]
  simpa only [vectorGerms, List.map_ofFn, Function.comp_def] using section_head_ideal V B C hCB x hxC n r s a ha

theorem analyticOpen_mono (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {B C : V.carrier.Opens} (h : C ≤ B) :
    Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver C ≤ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver B := fun _ hx => h hx

theorem analyticOpen_le_baseRange (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B : V.carrier.Opens) :
    (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver B : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)) := by
  intro y hy
  refine ⟨(Scheme.SectionEvaluation.Constructions.openPointHomeomorph V.toOver B).symm ⟨y, hy⟩, ?_⟩
  exact congrArg Subtype.val ((Scheme.SectionEvaluation.Constructions.openPointHomeomorph V.toOver B).apply_symm_apply ⟨y, hy⟩)

end AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms

end

end OAI

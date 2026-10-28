import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ClosedSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Support Closure -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportClosure

noncomputable section

section

/-! Restricting a reduced integral support along an open immersion
gives an actual open immersion of reduced support schemes, constructed
from the native scheme pullback. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Restriction

variable {X Y : Scheme} (j : Y ⟶ X) [IsOpenImmersion j] (C : IrreducibleCloseds X)
  (h : (j ⁻¹' (C : Set X)).Nonempty)

abbrev model : Scheme := pullback j (CycleClass.Geometric.GenericPoint.reducedSupportι C)

omit [IsOpenImmersion j] in
include h in
theorem nonempty : Nonempty (model j C) := by
  obtain ⟨y, hy⟩ := h
  have hr : y ∈ Set.range (pullback.fst j (CycleClass.Geometric.GenericPoint.reducedSupportι C)) := by
    rw [Scheme.Pullback.range_fst, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact hy
  obtain ⟨z, _⟩ := hr
  exact ⟨z⟩

include h in
theorem integral : IsIntegral (model j C) := by
  let : Nonempty (model j C) := Restriction.nonempty j C h
  exact isIntegral_of_isOpenImmersion (pullback.snd j (CycleClass.Geometric.GenericPoint.reducedSupportι C))

def support : IrreducibleCloseds Y :=
  letI := integral j C h
  Closed.ImmersionSupport.support (pullback.fst j (CycleClass.Geometric.GenericPoint.reducedSupportι C))

theorem support_coe : (support j C h : Set Y) = j ⁻¹' (C : Set X) := by
  let := integral j C h
  change (Closed.ImmersionSupport.support (pullback.fst j (CycleClass.Geometric.GenericPoint.reducedSupportι C)) : Set Y) = _
  rw [Flat.ClosedSupport.support_range, Scheme.Pullback.range_fst, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

def iso : CycleClass.Geometric.GenericPoint.reducedSupportScheme (support j C h) ≅ model j C :=
  letI := integral j C h
  (Closed.ImmersionSupport.supportIso (pullback.fst j (CycleClass.Geometric.GenericPoint.reducedSupportι C))).symm

theorem iso_fst : (iso j C h).hom ≫ pullback.fst j (CycleClass.Geometric.GenericPoint.reducedSupportι C) =
    CycleClass.Geometric.GenericPoint.reducedSupportι (support j C h) := by
  let := integral j C h
  apply (cancel_epi (iso j C h).inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact (Closed.ImmersionSupport.supportIso_fac (pullback.fst j (CycleClass.Geometric.GenericPoint.reducedSupportι C))).symm

def map : CycleClass.Geometric.GenericPoint.reducedSupportScheme (support j C h) ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme C :=
  (iso j C h).hom ≫ pullback.snd j (CycleClass.Geometric.GenericPoint.reducedSupportι C)

instance map_open : IsOpenImmersion (map j C h) := by
  unfold map
  infer_instance

theorem map_fac : map j C h ≫ CycleClass.Geometric.GenericPoint.reducedSupportι C = CycleClass.Geometric.GenericPoint.reducedSupportι (support j C h) ≫ j := by
  rw [map, Category.assoc, ← pullback.condition, ← Category.assoc, iso_fst]

theorem map_range : Set.range (map j C h) = (CycleClass.Geometric.GenericPoint.reducedSupportι C) ⁻¹' Set.range j := by
  change Set.range (pullback.snd j (CycleClass.Geometric.GenericPoint.reducedSupportι C) ∘ (iso j C h).hom) = _
  rw [Set.range_comp, (iso j C h).hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_snd]

end Restriction

end

section

/-! An integral closed support in an open scheme maps openly into
its actual reduced closure, preserving its ambient embedding and
function-field dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme} (j : Y ⟶ X) [IsOpenImmersion j] (D : IrreducibleCloseds Y)

def closure : IrreducibleCloseds X := CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ j)

omit [IsOpenImmersion j] in
theorem closure_coe : (SupportClosure.closure j D : Set X) = _root_.closure (j '' (D : Set Y)) := by
  rw [SupportClosure.closure, CycleClass.Geometric.StratumClosure.integralImageClosure_coe]
  change _root_.closure (Set.range (j ∘ CycleClass.Geometric.GenericPoint.reducedSupportι D)) = _
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

theorem preimage : j ⁻¹' (SupportClosure.closure j D : Set X) = (D : Set Y) := by
  rw [closure_coe]
  have h := j.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image (D : Set Y)
  rw [D.isClosed.closure_eq] at h
  exact h.symm

theorem nonempty : (j ⁻¹' (SupportClosure.closure j D : Set X)).Nonempty :=
  (preimage j D).symm ▸ D.isIrreducible.nonempty

theorem source_eq : Restriction.support j (SupportClosure.closure j D) (SupportClosure.nonempty j D) = D := by
  apply IrreducibleCloseds.ext
  rw [Restriction.support_coe, preimage]

theorem inclusion_congr {Z : Scheme} (C E : IrreducibleCloseds Z) (h : C = E) :
    eqToHom (congrArg CycleClass.Geometric.GenericPoint.reducedSupportScheme h) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι E = CycleClass.Geometric.GenericPoint.reducedSupportι C := by
  subst E
  simp

theorem range_eqToHom_comp {A B C : Scheme} (h : A = B) (f : B ⟶ C) :
    Set.range (eqToHom h ≫ f) = Set.range f := by
  subst B
  simp

def map : CycleClass.Geometric.GenericPoint.reducedSupportScheme D ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportClosure.closure j D) :=
  eqToHom (congrArg CycleClass.Geometric.GenericPoint.reducedSupportScheme (source_eq j D).symm) ≫
    Restriction.map j (SupportClosure.closure j D) (SupportClosure.nonempty j D)

instance map_open : IsOpenImmersion (map j D) := by
  unfold map
  infer_instance

theorem map_fac : map j D ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (SupportClosure.closure j D) = CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ j := by
  rw [map, Category.assoc, Restriction.map_fac, ← Category.assoc,
    inclusion_congr D _ (source_eq j D).symm]

theorem map_range : Set.range (map j D) = (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportClosure.closure j D)) ⁻¹' Set.range j := by
  rw [map, range_eqToHom_comp, Restriction.map_range]

theorem dimension [QuasiCompact j] {k : Type} [Field k] (f : X ⟶ Spec (.of k)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (j ≫ f) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension (SupportClosure.closure j D) f := by
  have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ j) f
  simpa only [SupportClosure.closure, Foundations.Scheme.SupportDimension.supportTranscendenceDimension, CycleClass.Geometric.SupportFiniteType.supportStructureMap, Category.assoc] using h

end

/-! In an actual open base-change square, the reduced closure of
a support retains every point over a parameter lying in the open base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Pullback

variable {X Y U B : Scheme} (j : Y ⟶ X) (u : Y ⟶ U) (t : X ⟶ B) (v : U ⟶ B)
  (h : IsPullback j u t v)

include h in
theorem range : Set.range j = t ⁻¹' Set.range v := by
  rw [← h.isoPullback_hom_fst]
  change Set.range (pullback.fst t v ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

variable [IsOpenImmersion j] (D : IrreducibleCloseds Y)

include h in
theorem covers (b : B) (hb : b ∈ Set.range v)
    (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportClosure.closure j D))
    (hz : (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportClosure.closure j D) ≫ t) z = b) :
    z ∈ Set.range (map j D) := by
  rw [map_range, SupportClosure.Pullback.range j u t v h]
  change t (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportClosure.closure j D) z) ∈ Set.range v
  rw [show t (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportClosure.closure j D) z) = b from hz]
  exact hb

end Pullback

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportClosure

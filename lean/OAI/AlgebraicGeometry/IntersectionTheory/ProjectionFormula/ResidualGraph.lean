import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnramifiedOpenFactor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Residual Graph -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualGraph

noncomputable section

section

/-! The original support is an open subscheme in the relevant
fiber product over an etale neighborhood. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y Z : Scheme} (π : X ⟶ Y) (i : Z ⟶ X) (U : X.Opens)

def graph : ((i ⁻¹ᵁ U) : Scheme) ⟶ pullback (U.ι ≫ π) (i ≫ π) :=
  pullback.lift (i.resLE U (i ⁻¹ᵁ U) le_rfl) (i ⁻¹ᵁ U).ι
    (by rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc])

theorem graph_fst : graph π i U ≫ pullback.fst (U.ι ≫ π) (i ≫ π) =
    i.resLE U (i ⁻¹ᵁ U) le_rfl := pullback.lift_fst _ _ _

theorem graph_snd : graph π i U ≫ pullback.snd (U.ι ≫ π) (i ≫ π) =
    (i ⁻¹ᵁ U).ι := pullback.lift_snd _ _ _

instance graph_open [Etale (U.ι ≫ π)] : IsOpenImmersion (graph π i U) := by
  have hc : IsOpenImmersion (graph π i U ≫ pullback.snd (U.ι ≫ π) (i ≫ π)) := by
    rw [graph_snd]
    infer_instance
  let := hc
  exact UnramifiedOpenFactor.factor (graph π i U) (pullback.snd (U.ι ≫ π) (i ≫ π))

theorem fst_graph_mem (z : i ⁻¹ᵁ U) :
    U.ι (pullback.fst (U.ι ≫ π) (i ≫ π) (graph π i U z)) ∈ Set.range i := by
  have he := congrArg (fun f => f z) (graph_fst π i U)
  change U.ι ((graph π i U ≫ pullback.fst (U.ι ≫ π) (i ≫ π)) z) ∈ _
  rw [he]
  exact ⟨z.val, (Scheme.Hom.coe_resLE_apply i le_rfl z).symm⟩

end

section

/-! At a point isolated on its support fiber, the entire fiber in
the auxiliary fiber product lies in the open graph of the support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace FiberAtPoint

theorem graph_contains_fiber {X Y Z : Scheme} (π : X ⟶ Y) (i : Z ⟶ X)
    [IsFinite π] [IsClosedImmersion i] (t : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType t]
    (U : X.Opens) (x : U) (hx : IsClosed ({x.val} : Set X))
    (hsep : ∀ z : Z, π (i z) = π x.val → i z = x.val)
    (v : ↥(pullback (U.ι ≫ π) (i ≫ π)))
    (hv : pullback.fst (U.ι ≫ π) (i ≫ π) v = x) :
    v ∈ Set.range (graph π i U) := by
  let f := U.ι ≫ π
  let g := i ≫ π
  have hxU : IsClosed ({x} : Set U) := by
    have he : U.ι ⁻¹' ({x.val} : Set X) = ({x} : Set U) := by
      ext y
      exact Subtype.val_inj
    rw [← he]
    exact hx.preimage U.ι.continuous
  have hz : i (pullback.snd f g v) = x.val := by
    apply hsep
    have he := congrArg (fun a => a v) (pullback.condition (f := f) (g := g))
    change π (U.ι (pullback.fst f g v)) = π (i (pullback.snd f g v)) at he
    rw [hv] at he
    exact he.symm
  let z : i ⁻¹ᵁ U := ⟨pullback.snd f g v, by
    change i (pullback.snd f g v) ∈ U
    rw [hz]
    exact x.property⟩
  let w := graph π i U z
  have hfst : pullback.fst f g w = x := by
    apply Subtype.ext
    have he := congrArg (fun a => a z) (graph_fst π i U)
    change (pullback.fst f g w).val = x.val
    exact (congrArg (fun u : U => u.val) he).trans
      ((Scheme.Hom.coe_resLE_apply i le_rfl z).trans hz)
  have hsnd : pullback.snd f g w = pullback.snd f g v :=
    congrArg (fun a => a z) (graph_snd π i U)
  have hvc : IsClosed ({v} : Set _) :=
    Closed.FiberPoints.closed (pullback.fst f g) v (by rw [hv]; exact hxU)
  have hwc : IsClosed ({w} : Set _) :=
    Closed.FiberPoints.closed (pullback.fst f g) w (by rw [hfst]; exact hxU)
  have he : v = w := Closed.FiberPoints.pullback_ext f g t v w hvc hwc
    (hv.trans hfst.symm) hsnd.symm
  exact ⟨z, he.symm⟩

end FiberAtPoint

end

/-! Properness of the auxiliary projection excludes the residual
closed set from a neighborhood of a selected etale, isolated support point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Neighborhood

variable {X Y Z : Scheme} (π : X ⟶ Y) (i : Z ⟶ X)
  [IsFinite π] [IsClosedImmersion i]
  (t : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType t]
  (U : X.Opens) [Etale (U.ι ≫ π)]

include t in
theorem exists_open (x : X) (hx : IsClosed ({x} : Set _)) (hxU : x ∈ U)
    (hsep : ∀ z : Z, π (i z) = π x → i z = x) :
    ∃ V : X.Opens, x ∈ V ∧
      ∀ y ∈ V, π y ∈ Set.range (i ≫ π) → y ∈ Set.range i := by
  let f := U.ι ≫ π
  let g := i ≫ π
  let q := graph π i U
  let B : Set U := pullback.fst f g '' (Set.range q)ᶜ
  have hB : IsClosed B :=
    (pullback.fst f g).isClosedMap _ q.isOpenEmbedding.isOpen_range.isClosed_compl
  let V' : Opens U := ⟨Bᶜ, hB.isOpen_compl⟩
  let V : X.Opens := ⟨U.ι '' (V' : Set U), U.ι.isOpenEmbedding.isOpenMap _ V'.isOpen⟩
  have hxV : x ∈ V := by
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    rintro ⟨v, hv, hvx⟩
    exact hv (FiberAtPoint.graph_contains_fiber π i t U ⟨x, hxU⟩ hx hsep v hvx)
  refine ⟨V, hxV, ?_⟩
  rintro y ⟨u, hu, rfl⟩ ⟨z, hz⟩
  obtain ⟨v, hvu, hvz⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) u z hz.symm
  have hvq : v ∈ Set.range q := by
    by_contra hn
    exact hu ⟨v, hn, hvu⟩
  obtain ⟨w, hw⟩ := hvq
  have hm := fst_graph_mem π i U w
  rw [show graph π i U w = v from hw, hvu] at hm
  exact hm

include t in
theorem avoids_closure (x : X) (hx : IsClosed ({x} : Set _)) (hxU : x ∈ U)
    (hsep : ∀ z : Z, π (i z) = π x → i z = x) :
    x ∉ closure (π ⁻¹' Set.range (i ≫ π) \ Set.range i) := by
  obtain ⟨V, hxV, hV⟩ := exists_open π i t U x hx hxU hsep
  intro hc
  obtain ⟨y, hyV, hy, hyn⟩ := mem_closure_iff.mp hc (V : Set X) V.isOpen hxV
  exact hyn (hV y hyV hy)

end Neighborhood

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualGraph

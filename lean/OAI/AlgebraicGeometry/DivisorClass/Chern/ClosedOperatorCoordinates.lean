import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-! # Closed Operator Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedOperatorCoordinates

noncomputable section

/-! Native partially defined closed operators under actual continuous linear changes of coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {A B C D : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C] [NormedAddCommGroup D] [NormedSpace ℂ D]
  (e : A ≃L[ℂ] C) (f : B ≃L[ℂ] D) (T : C →ₗ.[ℂ] D)

def linearPMapCoordinateGraph : Submodule ℂ (A × B) :=
  T.graph.comap (e.prodCongr f).toLinearMap

theorem linearPMapCoordinateGraph_zero_source (z : A × B)
    (hz : z ∈ linearPMapCoordinateGraph e f T) (hs : z.1 = 0) : z.2 = 0 := by
  change (e z.1, f z.2) ∈ T.graph at hz
  have hf : f z.2 = 0 := T.graph_fst_eq_zero_snd hz (by rw [hs, map_zero])
  exact f.injective (hf.trans f.map_zero.symm)

def linearPMapInCoordinates : A →ₗ.[ℂ] B :=
  (linearPMapCoordinateGraph e f T).toLinearPMap

theorem linearPMapInCoordinates_graph :
    (linearPMapInCoordinates e f T).graph = linearPMapCoordinateGraph e f T :=
  Submodule.toLinearPMap_graph_eq _ (linearPMapCoordinateGraph_zero_source e f T)

theorem linearPMapInCoordinates_mem_graph (x : A) (y : B) :
    (x, y) ∈ (linearPMapInCoordinates e f T).graph ↔ (e x, f y) ∈ T.graph := by
  rw [linearPMapInCoordinates_graph]
  rfl

theorem linearPMapInCoordinates_isClosed (hT : T.IsClosed) :
    (linearPMapInCoordinates e f T).IsClosed := by
  change IsClosed ((linearPMapInCoordinates e f T).graph : Set (A × B))
  rw [linearPMapInCoordinates_graph]
  exact hT.preimage (e.prodCongr f).continuous

theorem linearPMapInCoordinates_mem_domain (x : A) :
    x ∈ (linearPMapInCoordinates e f T).domain ↔ e x ∈ T.domain := by
  rw [LinearPMap.mem_domain_iff, LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨f y, (linearPMapInCoordinates_mem_graph e f T x y).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨f.symm y, (linearPMapInCoordinates_mem_graph e f T x (f.symm y)).mpr (by simpa using hy)⟩

theorem linearPMapInCoordinates_domain_dense (hT : Dense (T.domain : Set C)) :
    Dense ((linearPMapInCoordinates e f T).domain : Set A) := by
  have he : ((linearPMapInCoordinates e f T).domain : Set A) = e ⁻¹' (T.domain : Set C) := by
    ext x
    exact linearPMapInCoordinates_mem_domain e f T x
  rw [he]
  exact hT.preimage e.toHomeomorph.isOpenMap

theorem linearPMapCoordinateGraph_closure_range {S : Type*} [AddCommGroup S] [Module ℂ S]
    (p : S →ₗ[ℂ] A × B) (q : S →ₗ[ℂ] C × D)
    (he : ∀ s, (e.prodCongr f) (p s) = q s)
    (hT : T.graph = (LinearMap.range q).topologicalClosure) :
    linearPMapCoordinateGraph e f T = (LinearMap.range p).topologicalClosure := by
  have hp : (e.prodCongr f) ⁻¹' Set.range q = Set.range p := by
    ext z
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, (e.prodCongr f).injective ((he s).trans hs)⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, (he s).symm⟩
  apply SetLike.coe_injective
  change (e.prodCongr f) ⁻¹' (T.graph : Set (C × D)) = closure (Set.range p)
  rw [hT]
  change (e.prodCongr f).toHomeomorph ⁻¹' closure (Set.range q) = closure (Set.range p)
  rw [(e.prodCongr f).toHomeomorph.preimage_closure]
  exact congrArg closure hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedOperatorCoordinates

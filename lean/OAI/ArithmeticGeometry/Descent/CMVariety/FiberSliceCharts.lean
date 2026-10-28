import OAI.ArithmeticGeometry.Descent.CMVariety.RegularSectionCharts
import Mathlib.Topology.ContinuousOn

/-! # Fiber Slice Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Restrict actual local product charts to actual topological fibers. The
fiber chart and its inverse are constructed, with explicit coordinate
formulas on the chart target. For smooth relative algebra characters,
regular-function evaluations in the fiber chart remain analytic.
-/

open Set
open scoped Classical ContDiff

theorem FiberSliceCharts.Abelian.exists_fiber_slice_chart
    {X S P V : Type} [TopologicalSpace X] [TopologicalSpace S]
    [TopologicalSpace P] [TopologicalSpace V]
    (p : X → S) (x₀ : X)
    (b : OpenPartialHomeomorph S P) (e : OpenPartialHomeomorph X (P × V))
    (hb : p x₀ ∈ b.source) (hx : x₀ ∈ e.source)
    (hmap : ∀ x ∈ e.source, p x ∈ b.source)
    (hproj : ∀ x ∈ e.source, (e x).1 = b (p x)) :
    ∃ c : OpenPartialHomeomorph {x : X // p x = p x₀} V,
      (⟨x₀, rfl⟩ : {x : X // p x = p x₀}) ∈ c.source ∧
      c.source = Subtype.val ⁻¹' e.source ∧
      c.target = {v | (b (p x₀), v) ∈ e.target} ∧
      (∀ x, c x = (e x.val).2) ∧
      ∀ v ∈ c.target, (c.symm v).val = e.symm (b (p x₀), v) := by
  let D := {v : V | (b (p x₀), v) ∈ e.target}
  have hfiber (v : V) (hv : v ∈ D) : p (e.symm (b (p x₀), v)) = p x₀ := by
    apply b.injOn (hmap _ (e.map_target hv)) hb
    rw [← hproj _ (e.map_target hv), e.right_inv hv]
  let inv : V → {x : X // p x = p x₀} := fun v =>
    if hv : v ∈ D then ⟨e.symm (b (p x₀), v), hfiber v hv⟩ else ⟨x₀, rfl⟩
  have hinv (v : V) (hv : v ∈ D) : (inv v).val = e.symm (b (p x₀), v) := by
    simp only [inv, dite_eq_left hv]
  have hfirst (x : {x : X // p x = p x₀}) (hx : x.val ∈ e.source) :
      (e x.val).1 = b (p x₀) := (hproj x.val hx).trans (congrArg b x.property)
  have htarget (x : {x : X // p x = p x₀}) (hx : x.val ∈ e.source) :
      (e x.val).2 ∈ D := by
    change (b (p x₀), (e x.val).2) ∈ e.target
    rw [← hfirst x hx]
    exact e.map_source hx
  let c : OpenPartialHomeomorph {x : X // p x = p x₀} V := {
    toFun := fun x => (e x.val).2
    invFun := inv
    source := Subtype.val ⁻¹' e.source
    target := D
    map_source' := fun x hx => htarget x hx
    map_target' := fun v hv => by
      change (inv v).val ∈ e.source
      rw [hinv v hv]
      exact e.map_target hv
    left_inv' := fun x hx => by
      apply Subtype.ext
      rw [hinv _ (htarget x hx), ← hfirst x hx]
      exact e.left_inv hx
    right_inv' := fun v hv => by
      rw [hinv v hv, e.right_inv hv]
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun :=
      (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).snd
    continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr <| by
      apply (e.symm.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ hv => hv)).congr
      intro v hv
      exact hinv v hv }
  exact ⟨c, hx, rfl, rfl, fun _ => rfl, hinv⟩

variable {R A E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A}

/-- The actual fiber of a smooth relative affine chart has a constructed
coordinate chart, with analytic evaluation of all original regular functions. -/
theorem SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.exists_fiber_chart
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F)) :
    ∃ c : OpenPartialHomeomorph
        {y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // y.comp (IsScalarTower.toAlgHom ℂ R A) =
          x.comp (IsScalarTower.toAlgHom ℂ R A)} E,
      (⟨x, rfl⟩ : {y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // y.comp (IsScalarTower.toAlgHom ℂ R A) =
        x.comp (IsScalarTower.toAlgHom ℂ R A)}) ∈ c.source ∧
      (∀ y, c y = (C.total y.val).2) ∧
      ∀ a : A, ContDiffOn ℂ ω (fun v => (c.symm v).val a) c.target := by
  have hmap (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hy : y ∈ C.total.source) :
      y.comp (IsScalarTower.toAlgHom ℂ R A) ∈ C.base.source := by
    simpa only [C.total.left_inv hy] using C.mapsTo _ (C.total.map_source hy)
  have hproj (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hy : y ∈ C.total.source) :
      (C.total y).1 = C.base (y.comp (IsScalarTower.toAlgHom ℂ R A)) := by
    simpa only [C.total.left_inv hy] using (C.projection _ (C.total.map_source hy)).symm
  obtain ⟨c, hc, _, htarget, hforward, hinv⟩ := FiberSliceCharts.Abelian.exists_fiber_slice_chart
    (fun y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => y.comp (IsScalarTower.toAlgHom ℂ R A)) x
    C.base C.total C.basePoint C.point hmap hproj
  refine ⟨c, hc, hforward, ?_⟩
  intro a
  have hpair : ContDiff ℂ ω
      (fun v : E => (C.base (x.comp (IsScalarTower.toAlgHom ℂ R A)), v)) :=
    contDiff_const.prodMk contDiff_id
  have hmem : MapsTo
      (fun v : E => (C.base (x.comp (IsScalarTower.toAlgHom ℂ R A)), v))
      c.target C.total.target := by
    intro v hv
    rw [htarget] at hv
    exact hv
  apply ((C.regularTotal a).comp hpair.contDiffOn hmem).congr
  intro v hv
  exact congrArg (fun y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => y a) (hinv v hv)

end

end OAI.ArithmeticGeometry.Descent.CMVariety

import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizationEq
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.IsLocalHomeomorph

/-! # Exponential Local -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential

noncomputable section

/-!
# DegreeTwo: local invertibility of the constructed exponential

The inverse function theorem is applied in the actual manifold chart at the
identity. Translation then gives local invertibility at every tangent vector.
-/

open _root_.Manifold _root_.Topology
open scoped _root_.Manifold ContDiff

/-- Replacing the irrelevant values outside a partial homeomorphism's source
does not change its inverse or its homeomorphism properties on that source. -/
def withFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (f : X → Y) (hf : Set.EqOn f e e.source) :
    OpenPartialHomeomorph X Y where
  toFun := f
  invFun := e.symm
  source := e.source
  target := e.target
  map_source' := fun x hx => hf hx ▸ e.map_source hx
  map_target' := fun _ hx => e.map_target hx
  left_inv' := fun x hx => by rw [hf hx]; exact e.left_inv hx
  right_inv' := fun y hy => by rw [hf (e.map_target hy)]; exact e.right_inv hy
  continuousOn_toFun := e.continuousOn.congr hf
  continuousOn_invFun := e.continuousOn_symm
  open_source := e.open_source
  open_target := e.open_target

variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace C] [ChartedSpace E C] [CommGroup C]
  [LieGroup (𝓘(ℝ, E)) ∞ C] [T2Space C]

/-- The inverse function theorem produces a genuine local inverse near zero. -/
theorem exists_expMap_localHomeomorph_zero :
    ∃ e : OpenPartialHomeomorph E C,
      (0 : E) ∈ e.source ∧ (e : E → C) = ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) := by
  let f := ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)
  let c := chartAt E (f 0)
  let g : E → E := extChartAt (𝓘(ℝ, E)) (f 0) ∘ f
  have hc : ContDiffAt ℝ 1 g (0 : E) :=
    ((contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := f 0) (n := 1)).comp
      0 (ExponentialM.Constructions.Exponential.expMap_contMDiff_one (E := E) (C := C) 0)).contDiffAt
  have hd : HasFDerivAt g
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) (0 : E) := by
    apply HasMFDerivAt.hasFDerivAt
    have hchart := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
      (mem_chart_source E (f 0))).hasMFDerivAt
    have h := hchart.comp 0 (ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero (E := E) (C := C))
    apply h.congr_mfderiv
    rw [mfderiv_extChartAt_self]
    ext x
    rfl
  let r := hc.toOpenPartialHomeomorph g hd (by norm_num)
  have hr₀ : (0 : E) ∈ r.source := hc.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have hcf₀ : f 0 ∈ c.source := mem_chart_source E (f 0)
  let k := (r.trans c.symm).restrOpen (f ⁻¹' c.source)
    (c.open_source.preimage (ExponentialM.Constructions.Exponential.expMap_continuous (E := E) (C := C)))
  have hk₀ : (0 : E) ∈ k.source := by
    refine ⟨⟨hr₀, ?_⟩, hcf₀⟩
    exact c.map_source hcf₀
  have heq : Set.EqOn f k k.source := by
    intro x hx
    change f x = c.symm (c (f x))
    exact (c.left_inv hx.2).symm
  exact ⟨withFun k f heq, hk₀, rfl⟩

/-- The constructed exponential is a local homeomorphism everywhere. -/
theorem expMap_isLocalHomeomorph :
    IsLocalHomeomorph (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) := by
  let : IsTopologicalGroup C := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  obtain ⟨e, he₀, he⟩ := exists_expMap_localHomeomorph_zero (E := E) (C := C)
  intro v
  let d := ((Homeomorph.subRight v).toOpenPartialHomeomorph.trans e).trans
    (Homeomorph.mulLeft (ExponentialM.Constructions.Exponential.expMap (C := C) v)).toOpenPartialHomeomorph
  refine ⟨d, ?_, ?_⟩
  · exact ⟨⟨Set.mem_univ v, by simpa using he₀⟩, Set.mem_univ _⟩
  · funext x
    change ExponentialM.Constructions.Exponential.expMap (C := C) x = ExponentialM.Constructions.Exponential.expMap (C := C) v * e (x - v)
    rw [he, ← ExponentialM.Constructions.Exponential.expMap_add]
    congr 1
    abel

/-- The exponential as an additive homomorphism into the additive spelling of
the commutative group. -/
def expAddHom : E →+ Additive C where
  toFun := fun v => Additive.ofMul (ExponentialM.Constructions.Exponential.expMap (C := C) v)
  map_zero' := ExponentialM.Constructions.Exponential.exp_zero (G := C)
  map_add' := ExponentialM.Constructions.Exponential.expMap_add (C := C)

/-- The actual period subgroup of the exponential. -/
def expLattice : Submodule ℤ E := (expAddHom (E := E) (C := C)).ker.toIntSubmodule

instance expLattice_discrete : DiscreteTopology (expLattice (E := E) (C := C)) :=
  UniformizationEq.Constructions.Uniformization.kernel_discrete (expAddHom (E := E) (C := C))
    (expMap_isLocalHomeomorph (E := E) (C := C))

/-- Connectedness gives surjectivity of the constructed exponential. -/
theorem expMap_surjective [ConnectedSpace C] :
    Function.Surjective (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) := by
  let : IsTopologicalGroup C := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  let : ConnectedSpace (Additive C) := ‹ConnectedSpace C›
  exact UniformizationEq.Constructions.Uniformization.surjective_of_localHomeomorph
    (expAddHom (E := E) (C := C)) (expMap_isLocalHomeomorph (E := E) (C := C))

/-- Compactness forces the actual periods to span the real tangent space. -/
instance expLattice_full [ConnectedSpace C] [CompactSpace C] :
    IsZLattice ℝ (expLattice (E := E) (C := C)) := by
  let : IsTopologicalGroup C := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  let : ConnectedSpace (Additive C) := ‹ConnectedSpace C›
  let : CompactSpace (Additive C) := ‹CompactSpace C›
  exact (UniformizationEq.Constructions.Uniformization.kernel_is_lattice (expAddHom (E := E) (C := C))
    (expMap_isLocalHomeomorph (E := E) (C := C))).choose_spec

/-- A compact connected commutative real Lie group is the quotient of its
tangent space by the periods of its constructed exponential. -/
def expQuotientHomeomorph [ConnectedSpace C] :
    (E ⧸ (expLattice (E := E) (C := C)).toAddSubgroup) ≃ₜ C := by
  let : IsTopologicalGroup C := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  exact UniformizationEq.Constructions.Uniformization.quotientHomeomorph (expAddHom (E := E) (C := C))
    (expMap_isLocalHomeomorph (E := E) (C := C))
    (expMap_surjective (E := E) (C := C))

@[simp]
theorem expQuotientHomeomorph_mk [ConnectedSpace C] (v : E) :
    expQuotientHomeomorph (C := C) (QuotientAddGroup.mk v) = ExponentialM.Constructions.Exponential.expMap (C := C) v := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential

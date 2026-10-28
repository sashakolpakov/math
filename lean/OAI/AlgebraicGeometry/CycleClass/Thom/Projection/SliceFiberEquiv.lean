import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality

/-! # Slice Fiber Equiv -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions.Support

/-! The actual support pulled back to a normal slice is precisely the finite fiber over its base point. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential.Constructions

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

def ambientSliceProduct (Y : TopCat.{0}) :
    TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × Y) ⟶ TopCat.of (N × Y) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P, 𝟙 Y) :
    (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P), Y) ⟶ (TopCat.of N, Y))

def sliceSupport (Y : TopCat.{0}) (T : Set (N × Y)) : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × Y) :=
  ambientSliceProduct P Y ⁻¹' T

theorem ambientSlice_mapsTo : Set.MapsTo (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) ({HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ)
    (Set.range f)ᶜ := fun _ hx => Normal.SliceDetection.Constructions.normalSliceMapsTo P hx

theorem sliceSupport_bound (Y : TopCat.{0}) (T : Set (N × Y)) (K : Set Y)
    (hT : T ⊆ Set.range f ×ˢ K) :
    sliceSupport P Y T ⊆ {HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P} ×ˢ K := by
  intro z hz
  have h := hT hz
  refine ⟨?_, h.2⟩
  by_contra hn
  exact ambientSlice_mapsTo P hn h.1

theorem sliceSupport_eq_fiber (Y : TopCat.{0}) (T : Set (N × Y))
    (hT : T ⊆ Set.range f ×ˢ Set.univ) :
    sliceSupport P Y T = {HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P} ×ˢ {u : Y | (f x, u) ∈ T} := by
  ext z
  constructor
  · intro hz
    have h0 : z.1 = HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P := (sliceSupport_bound P Y T Set.univ hT hz).1
    refine ⟨h0, ?_⟩
    change (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P z.1, z.2) ∈ T at hz
    rwa [h0, Normal.SliceDifferential.Constructions.normalSliceAmbient_origin] at hz
  · rintro ⟨h0, hz⟩
    change (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P z.1, z.2) ∈ T
    change z.1 = HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P at h0
    rwa [h0, Normal.SliceDifferential.Constructions.normalSliceAmbient_origin]

theorem sliceSupport_finite (Y : TopCat.{0}) (T : Set (N × Y))
    (hT : T ⊆ Set.range f ×ˢ Set.univ) (hfin : {u : Y | (f x, u) ∈ T}.Finite) :
    (sliceSupport P Y T).Finite := by
  rw [sliceSupport_eq_fiber P Y T hT]
  exact (Set.finite_singleton _).prod hfin

end AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions.Support

namespace AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions

/-! The points of the actual sliced support are exactly the source points in the projection fiber. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions.Support OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential.Constructions

variable {M L N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)
  (Y : TopCat.{0}) (i : L → N × Y)

omit [NormedSpace ℝ E] in
def fiberToSlice (z : {y : L | (i y).1 = f x}) : Support.sliceSupport P Y (Set.range i) :=
  ⟨(HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i z.val).2),
    ⟨z.val, Prod.ext (z.property.trans (Normal.SliceDifferential.Constructions.normalSliceAmbient_origin P).symm) rfl⟩⟩

omit [NormedSpace ℝ E] in
theorem fiberToSlice_injective (hi : Function.Injective i) : Function.Injective (fiberToSlice P Y i) := by
  intro a b hab
  apply Subtype.ext
  apply hi
  exact Prod.ext (a.property.trans b.property.symm)
    (congrArg (fun z : Support.sliceSupport P Y (Set.range i) => z.val.2) hab)

theorem fiberToSlice_surjective (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f) :
    Function.Surjective (fiberToSlice P Y i) := by
  intro z
  obtain ⟨y, hy⟩ := z.property
  have hT : Set.range i ⊆ Set.range f ×ˢ Set.univ := by
    rintro a ⟨b, rfl⟩
    exact ⟨hr ⟨b, rfl⟩, trivial⟩
  have h0 : z.val.1 = HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P := (Support.sliceSupport_bound P Y (Set.range i) Set.univ hT z.property).1
  have hxy : (i y).1 = f x := by
    have h := congrArg Prod.fst hy
    change (i y).1 = Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P z.val.1 at h
    rwa [h0, Normal.SliceDifferential.Constructions.normalSliceAmbient_origin] at h
  refine ⟨⟨y, hxy⟩, Subtype.ext ?_⟩
  change (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2) = z.val
  exact Prod.ext h0.symm (congrArg (fun a : N × Y => a.2) hy)

def sliceFiberEquiv (hi : Function.Injective i) (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f) :
    {y : L | (i y).1 = f x} ≃ Support.sliceSupport P Y (Set.range i) :=
  Equiv.ofBijective (fiberToSlice P Y i) ⟨fiberToSlice_injective P Y i hi, fiberToSlice_surjective P Y i hr⟩

theorem sliceFiber_card (hi : Function.Injective i) (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f)
    [Fintype {y : L | (i y).1 = f x}] [Fintype (Support.sliceSupport P Y (Set.range i))] :
    Fintype.card (Support.sliceSupport P Y (Set.range i)) = Fintype.card {y : L | (i y).1 = f x} :=
  (Fintype.card_congr (sliceFiberEquiv P Y i hi hr)).symm

end AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions

end

end OAI

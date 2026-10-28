import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalExt

/-! # Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.Projection.Constructions.ThomClass

noncomputable section

/-! A finite unramified projection of a closed holomorphic immersion pushes its actual Thom class to the fiber degree times the image Thom class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.LocalExt.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions.Support OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.ProjectedNormalRestriction
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M L N E G W : Type} [TopologicalSpace M] [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [ChartedSpace G N]
  [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] [ChartedSpace W L]
  [IsManifold 𝓘(ℂ, W) ω L] {c d : ℕ}

local instance (priority := low) : ChartedSpace (G × (Fin d → ℂ)) (N × (Fin d → ℂ)) :=
  prodChartedSpace G N (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, G × (Fin d → ℂ)) ω (N × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

theorem project_ThomClass (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f)
    (hfi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x))
    (hfe : Topology.IsClosedEmbedding f) (hfc : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = c)
    (i : L → N × (Fin d → ℂ))
    (hi : ContMDiff 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) ω i)
    (hii : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y))
    (he : Topology.IsClosedEmbedding i)
    (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension W (G × (Fin d → ℂ)) = c + d)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K) (hT : Set.range i ⊆ Set.range f ×ˢ K)
    (hip : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y))
    (hfin : ∀ x : M, Finite {y : L | (i y).1 = f x}) (m : ℕ)
    (hdeg : ∀ x : M, Nat.card {y : L | (i y).1 = f x} = m) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of N) (Set.range f) K hK (Set.range i) hT
      (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii he (c + d) hp) =
        (m : ℚ) • Degree.Constructions.ThomClass.complexThomClassInDegree f hf hfi hfe c hfc := by
  classical
  choose P hP hPa hPi using
    (fun x : M => FixedNormalPair.Constructions.exists_analytic_normalPair f hf hfi hfe.isEmbedding c hfc x)
  apply LocalExt.Constructions.ThomClass.normalPair_ext f hf hfi hfe c hfc P hP
  intro x
  let : Nonempty (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen (P x)) := ⟨HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin (P x)⟩
  let := hfin x
  let : Fintype {y : L | (i y).1 = f x} := Fintype.ofFinite _
  have hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f := by
    rintro a ⟨y, rfl⟩
    exact (hT ⟨y, rfl⟩).1
  let : Fintype (Projection.SliceFiberEquiv.Constructions.Support.sliceSupport (P x) (TopCat.of (Fin d → ℂ)) (Set.range i)) :=
    Fintype.ofEquiv _ (Projection.SliceFiberEquiv.Constructions.sliceFiberEquiv (P x) (TopCat.of (Fin d → ℂ)) i he.injective hr)
  let e : ((Fin c → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (c + d) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_prod, Module.finrank_fin_fun])
  have hc : Fintype.card (Projection.SliceFiberEquiv.Constructions.Support.sliceSupport (P x) (TopCat.of (Fin d → ℂ)) (Set.range i)) = m :=
    (Projection.SliceFiberEquiv.Constructions.sliceFiber_card (P x) (TopCat.of (Fin d → ℂ)) i he.injective hr).trans
      (Nat.card_eq_fintype_card.symm.trans (hdeg x))
  have h := Projection.SliceThom.Constructions.ProjectedNormalRestriction.projectedThomClass_normalRestriction (P x) i hi hii he hp (hP x) (hPi x)
    K hK hT (fun y _ => hip y) e
  rw [hc] at h
  rw [map_smul, Degree.Constructions.ThomClass.complexThomClassInDegree_restrict f hf hfi hfe c hfc x (P x) (hP x)]
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.Projection.Constructions.ThomClass

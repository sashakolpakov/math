import OAI.AlgebraicGeometry.CycleClass.Thom.ImageExteriorNormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion
import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget

/-! # Exterior Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorProduct.Constructions

noncomputable section

/-! Exterior products of the genuine global Thom classes of closed complex
immersions, with the actual product immersion and actual support. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalDifferentiable.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageExteriorNormalRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget.Constructions
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F G H M M' N N' : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace M'] [ChartedSpace F M'] [IsManifold 𝓘(ℂ, F) ω M']
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N']

local instance (priority := low) : ChartedSpace (E × F) (M × M') := Product.Immersion.Constructions.productModelCharted E M F M'
local instance (priority := low) : ChartedSpace (G × H) (N × N') := Product.Immersion.Constructions.productModelCharted G N H N'
local instance : IsManifold 𝓘(ℂ, E × F) ω (M × M') :=
  Product.Immersion.Constructions.productModel_isManifold (E := E) (F := F) (M := M) (M' := M')
local instance : IsManifold 𝓘(ℂ, G × H) ω (N × N') :=
  Product.Immersion.Constructions.productModel_isManifold (E := G) (F := H) (M := N) (M' := N')
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F

variable (u : M → N) (v : M' → N')
  (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω u)
  (hv : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, H) ω v)
  (hiu : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) u x))
  (hiv : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, H) v x))
  (heu : Topology.IsClosedEmbedding u) (hev : Topology.IsClosedEmbedding v)
  (hEG : Module.finrank ℂ E ≤ Module.finrank ℂ G)
  (hFH : Module.finrank ℂ F ≤ Module.finrank ℂ H)

theorem complexThomClass_exteriorProduct :
    ExteriorImageCup.Constructions.imageExteriorCup u v heu.isClosed_range.isOpen_compl hev.isClosed_range.isOpen_compl
      (Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G) (Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension F H)
      (Geometric.ComplexThom.Cycles.complexThomClass u hu hiu heu) (Geometric.ComplexThom.Cycles.complexThomClass v hv hiv hev) =
    Degree.Constructions.ThomClass.complexThomClassInDegree (Prod.map u v) (Product.Immersion.Constructions.productImmersion_contMDiff u v hu hv)
      (Product.Immersion.Constructions.productImmersion_injective_mfderiv u v hu hv hiu hiv) (heu.prodMap hev)
      (Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G + Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension F H)
      (Product.Immersion.Constructions.complexImmersionCodimension_prod hEG hFH) := by
  let p := Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G
  let q := Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension F H
  let e := HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates p q
  let P := Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair u hu hiu heu
  let Q := Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair v hv hiv hev
  let R := fun z : M × M' => Product.NormalPair.Constructions.productNormalPair (P z.1) (Q z.2) e
  have hR : ∀ z, (R z).ambientChart.MDifferentiable
      𝓘(ℂ, G × H) 𝓘(ℂ, (E × F) × (Fin (p + q) → ℂ)) := by
    intro z
    rw [modelWithCornersSelf_prod]
    exact Product.NormalDifferentiable.Constructions.productNormalPair_mdifferentiable (P z.1) (Q z.2) e
      (Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable u hu hiu heu z.1)
      (Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable v hv hiv hev z.2)
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique (Prod.map u v) (Product.Immersion.Constructions.productImmersion_contMDiff u v hu hv)
    (Product.Immersion.Constructions.productImmersion_injective_mfderiv u v hu hv hiu hiv) (heu.prodMap hev) (p + q)
    (Product.Immersion.Constructions.complexImmersionCodimension_prod hEG hFH) R hR
  intro z
  exact ImageExteriorNormalRestriction.Constructions.imageExteriorCup_normal_restriction (P z.1) (Q z.2) e
    heu.isClosed_range.isOpen_compl hev.isClosed_range.isOpen_compl
    (Geometric.ComplexThom.Cycles.complexThomClass u hu hiu heu) (Geometric.ComplexThom.Cycles.complexThomClass v hv hiv hev)
    (Geometric.ComplexThom.Cycles.complexThomClass_restrict u hu hiu heu z.1)
    (Geometric.ComplexThom.Cycles.complexThomClass_restrict v hv hiv hev z.2)

/-- The same actual product formula when codimensions are displayed by
proved equalities, as for the native regular loci of algebraic cycles. -/
theorem complexThomClassInDegree_exteriorProduct (p q : ℕ)
    (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p)
    (hq : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension F H = q) :
    ExteriorImageCup.Constructions.imageExteriorCup u v heu.isClosed_range.isOpen_compl hev.isClosed_range.isOpen_compl p q
      (Degree.Constructions.ThomClass.complexThomClassInDegree u hu hiu heu p hp)
      (Degree.Constructions.ThomClass.complexThomClassInDegree v hv hiv hev q hq) =
    Degree.Constructions.ThomClass.complexThomClassInDegree (Prod.map u v) (Product.Immersion.Constructions.productImmersion_contMDiff u v hu hv)
      (Product.Immersion.Constructions.productImmersion_injective_mfderiv u v hu hv hiu hiv) (heu.prodMap hev) (p + q)
      ((Product.Immersion.Constructions.complexImmersionCodimension_prod hEG hFH).trans (congrArg₂ (· + ·) hp hq)) := by
  subst hp
  subst hq
  exact complexThomClass_exteriorProduct u v hu hv hiu hiv heu hev hEG hFH

/-- In ordinary cohomology this is precisely the cup of the two actual
projection pullbacks of the factor Thom classes. -/
theorem complexThomClassInDegree_absoluteProduct (p q : ℕ)
    (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p)
    (hq : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension F H = q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (N × N'))
      (Set.range (Prod.map u v))ᶜ (2 * (p + q))
      (Degree.Constructions.ThomClass.complexThomClassInDegree (Prod.map u v) (Product.Immersion.Constructions.productImmersion_contMDiff u v hu hv)
        (Product.Immersion.Constructions.productImmersion_injective_mfderiv u v hu hv hiu hiv) (heu.prodMap hev) (p + q)
        ((Product.Immersion.Constructions.complexImmersionCodimension_prod hEG hFH).trans (congrArg₂ (· + ·) hp hq))) =
    ExteriorCupForget.Constructions.evenAbsoluteExteriorCup (TopCat.of N) (TopCat.of N') p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p)
        (Degree.Constructions.ThomClass.complexThomClassInDegree u hu hiu heu p hp))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range v)ᶜ (2 * q)
        (Degree.Constructions.ThomClass.complexThomClassInDegree v hv hiv hev q hq)) := by
  rw [← complexThomClassInDegree_exteriorProduct u v hu hv hiu hiv heu hev hEG hFH p q hp hq]
  exact ExteriorCupForget.Constructions.imageExteriorCup_forget u v heu.isClosed_range.isOpen_compl hev.isClosed_range.isOpen_compl
    p q (Degree.Constructions.ThomClass.complexThomClassInDegree u hu hiu heu p hp) (Degree.Constructions.ThomClass.complexThomClassInDegree v hv hiv hev q hq)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorProduct.Constructions

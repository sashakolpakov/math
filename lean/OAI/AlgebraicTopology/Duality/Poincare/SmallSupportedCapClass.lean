import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCap
import OAI.AlgebraicTopology.Duality.Poincare.SupportCapNaturality
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Small Supported Cap Class -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCapClass

noncomputable section

/-!
# Local homology class of the cap product on small chains

The genuine binary small-chain pushout identifies its quotient by chains in
`A` with the relative chains of `(U, U ∩ A)`. This gives a canonical local
relative representative. Inclusion of that relative complex into `(X,A)` is
monic degreewise, so an ambient relative cycle is already a local relative
cycle. The resulting cap class is identified inside the homology of `U`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The actual small-relative inclusion is monic: its short-exact comparison
is the identity on chains in the excluded subspace and monic on all chains. -/
theorem binarySmallRelativeInclusion_mono (X : TopCat.{0}) (U A : Set X) :
    Mono (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.binarySmallRelativeInclusion X U A) := by
  let : Mono (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A) := by
    rw [AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
    infer_instance
  exact ShortComplex.mono_of_epi_of_epi_of_mono
    (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.binarySmallRelativeSequenceMap X U A)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_shortExact X A).exact
    (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.binarySmallRelativeSequence_shortExact X U A).epi_g
    (by change Epi (𝟙 (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A))); infer_instance)
    (by change Mono (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A); infer_instance)

/-- Inclusion of a subspace and the induced excluded subspace is injective
on the genuine relative chain complexes. -/
theorem relativeCoverInclusion_mono (X : TopCat.{0}) (U A : Set X) :
    Mono (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion X U A) := by
  let : Mono (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.binarySmallRelativeInclusion X U A) :=
    binarySmallRelativeInclusion_mono X U A
  rw [← AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion_factor]
  infer_instance

/-- Quotient a binary-small chain by `A` and use the proved pushout
identification to obtain an actual relative chain in `U`. -/
def smallRelativeLocalProjection (X : TopCat.{0}) (U A : Set X) :
    AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A ⟶
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) :=
  AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.binarySmallRelativeProjection X U A ≫ (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverCokernelIso X U A).inv

/-- The local relative representative includes to the ambient relative
projection of precisely the original small chain. -/
@[reassoc]
theorem smallRelativeLocalProjection_inclusion (X : TopCat.{0}) (U A : Set X) :
    smallRelativeLocalProjection X U A ≫ AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion X U A =
      AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A := by
  dsimp only [smallRelativeLocalProjection]
  rw [Category.assoc, ← AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion_factor]
  change AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.binarySmallRelativeProjection X U A ≫
      ((AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverCokernelIso X U A).inv ≫
        ((AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverCokernelIso X U A).hom ≫ AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.binarySmallRelativeInclusion X U A)) = _
  rw [Iso.inv_hom_id_assoc, AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.binarySmallRelativeInclusion_projection]

private theorem mem_chainCycles_of_monic_map
    {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) [Mono f]
    (n : ℕ) (z : C.X n) (hz : f.f n z ∈ Cohomology.Singular.ChainRepresentatives.chainCycles D n) : z ∈ Cohomology.Singular.ChainRepresentatives.chainCycles C n := by
  cases n with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero C z
  | succ n =>
    apply (Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ C n z).mpr
    have hf : Function.Injective (f.f n) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hf
    rw [map_zero]
    have hc := ConcreteCategory.congr_hom (f.comm (n + 1) n) z
    change D.d (n + 1) n (f.f (n + 1) z) = f.f n (C.d (n + 1) n z) at hc
    rw [← hc]
    exact (Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ D n (f.f (n + 1) z)).mp hz

/-- If the ambient relative projection is a cycle, its canonical local
relative representative is a cycle as well. -/
theorem smallRelativeLocalProjection_mem_chainCycles
    (X : TopCat.{0}) (U A : Set X) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X n)
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f n z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    (smallRelativeLocalProjection X U A).f n z ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A)) n := by
  let : Mono (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion X U A) := relativeCoverInclusion_mono X U A
  apply mem_chainCycles_of_monic_map (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion X U A) n
  have h := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (smallRelativeLocalProjection_inclusion X U A) n) z
  change (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion X U A).f n
      ((smallRelativeLocalProjection X U A).f n z) =
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f n z) at h
  rw [h]
  exact hz

/-- The canonical local relative cycle represented by the given small chain. -/
def smallRelativeLocalCycle
    (X : TopCat.{0}) (U A : Set X) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X n)
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f n z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of U)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A)) n :=
  ⟨(smallRelativeLocalProjection X U A).f n z,
    smallRelativeLocalProjection_mem_chainCycles X U A n z hz⟩

/-- The locally constructed small cap is exactly the genuine relative cap
of the canonical local relative representative, already at chain level. -/
theorem smallSupportedCap_eq_relativeCap
    (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q)) :
    SmallSupportedCap.smallSupportedCap X U A p q c z =
      SupportRelativeCap.relativeCap (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) p q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ hx => hx)).f p c)
        ((smallRelativeLocalProjection X U A).f (p + q) z) := by
  apply SmallSupportedCap.rationalSubspaceChainInclusion_injective X U q
  have h := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (smallRelativeLocalProjection_inclusion X U A) (p + q)) z
  change (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion X U A).f (p + q)
      ((smallRelativeLocalProjection X U A).f (p + q) z) =
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z) at h
  have hn := SupportCapNaturality.relativeCap_naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)
    (A := ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A)) (B := A)
    (fun _ hx => hx) p q c ((smallRelativeLocalProjection X U A).f (p + q) z)
  exact (SmallSupportedCap.smallSupportedCap_inclusion X U A p q c z).trans
    ((SupportRelativeCap.relativeCap_projection X A p q c
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z)).symm.trans
        ((congrArg (SupportRelativeCap.relativeCap X A p q c) h).symm.trans hn.symm))

/-- The canonical local relative cycle has exactly the original ambient
relative cycle as its image. -/
theorem smallRelativeLocalCycle_inclusion
    (X : TopCat.{0}) (U A : Set X) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X n)
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f n z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion X U A) n
        (smallRelativeLocalCycle X U A n z hz) =
      ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f n z), hz⟩ := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (smallRelativeLocalProjection_inclusion X U A) n) z

/-- The same identity on the actual relative homology classes. -/
theorem smallRelativeLocalCycle_class_inclusion
    (X : TopCat.{0}) (U A : Set X) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X n)
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f n z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion X U A) n)
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of U)
          ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A)) n
          (smallRelativeLocalCycle X U A n z hz)) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n
        ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
          ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f n z), hz⟩ := by
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality, smallRelativeLocalCycle_inclusion]

/-- A relative cocycle caps a small chain whose ambient relative projection
is closed to a genuine local rational cycle. -/
theorem smallSupportedCap_mem_chainCycles_of_relative
    (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    SmallSupportedCap.smallSupportedCap X U A p q c.val z ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)) q := by
  rw [smallSupportedCap_eq_relativeCap]
  exact SupportRelativeCap.relativeCap_mem_chainCycles (TopCat.of U)
    ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) p q
    (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ hx => hx)) p c)
    (smallRelativeLocalCycle X U A (p + q) z hz)

/-- The actual local cap cycle associated to an ambient relative cycle. -/
def smallSupportedRelativeCapCycle
    (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)) q :=
  ⟨SmallSupportedCap.smallSupportedCap X U A p q c.val z,
    smallSupportedCap_mem_chainCycles_of_relative X U A p q c z hz⟩

@[simp]
theorem smallSupportedRelativeCapCycle_val
    (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    (smallSupportedRelativeCapCycle X U A p q c z hz).val =
      SmallSupportedCap.smallSupportedCap X U A p q c.val z := rfl

/-- The class identity is already in the homology of the open piece,
with the canonical local relative representative. -/
theorem smallSupportedRelativeCapCycle_class
    (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q) z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)) q
        (smallSupportedRelativeCapCycle X U A p q c z hz) =
      SupportRelativeCap.relativeCapHomology (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) p q
        ((HomologicalComplex.homologyMap
          (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
            (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ hx => hx)) p)
          (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c))
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of U)
          ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A)) (p + q)
          (smallRelativeLocalCycle X U A (p + q) z hz)) := by
  let f := Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)
    (show Set.MapsTo (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) A
      from fun _ hx => hx)
  let cu := Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap f p c
  let zu := smallRelativeLocalCycle X U A (p + q) z hz
  have hv : smallSupportedRelativeCapCycle X U A p q c z hz =
      SupportRelativeCap.relativeCapCycles (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) p q cu zu := by
    apply Subtype.ext
    exact smallSupportedCap_eq_relativeCap X U A p q c.val z
  have hc := Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality f p c
  have hcap := SupportRelativeCap.relativeCapHomology_class_class (TopCat.of U)
    ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) p q cu zu
  exact (congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)) q) hv).trans
    (hcap.symm.trans (congrArg
      (fun a => SupportRelativeCap.relativeCapHomology (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) p q a
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of U)
          ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A)) (p + q) zu)) hc.symm))

/-- The actual local relative class is the inverse-excised ambient class.
The cancellation here uses the proved relative excision isomorphism. -/
theorem smallRelativeLocalCycle_class_excision
    (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U Kᶜ).X n)
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U Kᶜ).f n z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Kᶜ) n) :
    Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ)) n
        (smallRelativeLocalCycle X U Kᶜ n z hz) =
      (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU n).inv
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Kᶜ) n
          ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n
            ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U Kᶜ).f n z), hz⟩) := by
  let e := AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU n
  apply e.toLinearEquiv.injective
  change e.hom _ = e.hom (e.inv _)
  rw [show e.hom (e.inv _) = _ from e.toLinearEquiv.apply_symm_apply _]
  exact smallRelativeLocalCycle_class_inclusion X U Kᶜ n z hz

/-- The local small-cap homology class is exactly relative cap with the
restricted cohomology class and the inverse-excised ambient relative class. -/
theorem smallSupportedRelativeCapCycle_class_excision
    (X : TopCat.{0}) [T2Space X] (U K : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ) p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U Kᶜ).X (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U Kᶜ).f (p + q) z) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Kᶜ) (p + q)) :
    Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)) q
        (smallSupportedRelativeCapCycle X U Kᶜ p q c z hz) =
      SupportRelativeCap.relativeCapHomology (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) p q
        ((HomologicalComplex.homologyMap (CompactSupportExcision.compactSupportExcisionCochainMap X U K) p)
          (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ) p c))
        ((AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X U K hK hU hKU (p + q)).inv
          (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Kᶜ) (p + q)
            ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f (p + q)
              ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U Kᶜ).f (p + q) z), hz⟩)) := by
  exact (smallSupportedRelativeCapCycle_class X U Kᶜ p q c z hz).trans
    (congrArg
      (SupportRelativeCap.relativeCapHomology (TopCat.of U) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) p q
        ((HomologicalComplex.homologyMap (CompactSupportExcision.compactSupportExcisionCochainMap X U K) p)
          (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ) p c)))
      (smallRelativeLocalCycle_class_excision X U K hK hU hKU (p + q) z hz))

end

end OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCapClass

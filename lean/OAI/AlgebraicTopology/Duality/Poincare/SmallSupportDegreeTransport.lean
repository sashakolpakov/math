import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportRepresentatives
import OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisChains
import OAI.AlgebraicTopology.Products.ChainDegreeTransport

/-! # Small Support Degree Transport -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SmallSupportDegreeTransport

noncomputable section

/-!
# Degree transport for the common small-support representative

Transport along equality of degrees commutes with the actual relative
projection, preserves the actual cycle condition, and induces the ordinary
equality transport of the native homology class. No geometric assumption is
needed for these identities.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.ChainDegreeTransport.Cohomology

variable (X : TopCat.{0}) (U V K L A : Set X) {m n : ℕ}

/-- The actual relative projection commutes with the existing small-chain degree cast. -/
@[simp]
theorem smallSupportRelativeProjection_cast (h : m = n)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m) :
    (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f n
        (CapMayerVietorisChains.smallSupportChainCast X U V K L h s) =
      SupportRelativeCap.relativeChainCast X A h
        ((SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s) := by
  subst n
  rfl

/-- A degree cast preserves and reflects the actual projected-cycle condition. -/
theorem smallSupportProjectedCycle_cast_iff (h : m = n)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m) :
    (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f n
        (CapMayerVietorisChains.smallSupportChainCast X U V K L h s) ∈
          Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n ↔
      (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) m := by
  subst n
  rfl

/-- The projected cast is a cycle whenever the original projected chain is a cycle. -/
theorem smallSupportProjectedCycle_cast_mem (h : m = n)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m)
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) m) :
    (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f n
      (CapMayerVietorisChains.smallSupportChainCast X U V K L h s) ∈
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n :=
  (smallSupportProjectedCycle_cast_iff X U V K L A h s).mpr hs

/-- The actual projected-cycle representative itself is the canonical transported cycle. -/
theorem smallSupportProjectedCycle_cast (h : m = n)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m)
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) m) :
    (⟨(SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f n
        (CapMayerVietorisChains.smallSupportChainCast X U V K L h s),
      smallSupportProjectedCycle_cast_mem X U V K L A h s hs⟩ :
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) =
      Products.ChainDegreeTransport.Cohomology.chainCycleCast (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) h
        ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s, hs⟩ := by
  subst n
  rfl

/-- The native class of the projected cast is the canonical homology degree cast. -/
theorem smallSupportProjectedClass_cast (h : m = n)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m)
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) m) :
    Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n
        ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f n
          (CapMayerVietorisChains.smallSupportChainCast X U V K L h s),
          smallSupportProjectedCycle_cast_mem X U V K L A h s hs⟩ =
      Products.ChainDegreeTransport.Cohomology.chainHomologyCast (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) h
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) m
          ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s, hs⟩) := by
  subst n
  rfl

/-- The class formula written literally as equality transport in categorical homology. -/
theorem smallSupportProjectedClass_cast_eqToHom (h : m = n)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X m)
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) m) :
    Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n
        ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f n
          (CapMayerVietorisChains.smallSupportChainCast X U V K L h s),
          smallSupportProjectedCycle_cast_mem X U V K L A h s hs⟩ =
      (eqToHom (congrArg (fun i => (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).homology i) h))
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) m
          ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L A).f m s, hs⟩) := by
  subst n
  rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.SmallSupportDegreeTransport

import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison

/-! # Active Ambient Comparison Data -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting

/-! Embed the constructed coordinate kernel through an actual source
group homomorphism while retaining the original parameter family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {S : Scheme} {k : Type} [Field k]
  {f : Spec (.of k) ⟶ S} {G H : Grp (Over S)} [IsCommMonObj G.X]
  {q : ℕ} [Fact q.Prime] [Module (ZMod q) (Additive (Over.mk f ⟶ G.X))]
  {C : GenericActiveCoordinateData.ActiveCoordinateData f G q} {r : ℕ} {I B : Type}
  {F : I → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X (Over.mk f)}
  (D : CoordinateKernelDetection.Parameters.CoordinateKernelParameters C r I F) [Finite B]
  (split : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) B ≅ (Over.pullback f).obj G.X)
  (g : G ⟶ H)

local instance CoordinateKernelDetection.Parameters.CoordinateKernelParameters.pulledBackHom : IsMonHom ((Over.pullback f).map g.hom.hom) :=
  Functor.map.instIsMonHom (F := Over.pullback f) (f := g.hom.hom) G.X H.X

include split in
theorem CoordinateKernelDetection.Parameters.CoordinateKernelParameters.image_kernel_eq (i : I) :
    Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 (Spec (.of k))))
      ((C.kernel (D.enumeration i).val).inclusion ≫ (Over.pullback f).map g.hom.hom) =
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter H (Over.mk f) (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage g.hom.hom (F i)) :=
  Parameter.ImageComparison.parameter_kernel_image G H (Over.mk f) g (F i) (C.kernel (D.enumeration i).val).inclusion
    (D.kernel_eq split i)

end AlgebraicGeometry.Isogenies.NeighborCounting

namespace AlgebraicGeometry.Isogenies.NeighborCounting.ActiveAmbientComparisonData

/-! Index ambient active-family transport by the same complete coordinate
record that constructs the original parameter kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {S : Scheme} {k : Type} [Field k] {f : Spec (.of k) ⟶ S}
  {G A : Grp (Over S)} [IsCommMonObj G.X] {q : ℕ}
  [Module (ZMod q) (Additive (Over.mk f ⟶ G.X))]
  (C : GenericActiveCoordinateData.ActiveCoordinateData f G q) (i : G ⟶ A)

local instance pulledBackHom : IsMonHom ((Over.pullback f).map i.hom.hom) :=
  Functor.map.instIsMonHom (F := Over.pullback f) (f := i.hom.hom) G.X A.X

def coordinateAmbientKernelFamily (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback f).mapGrp.obj A).X (Over.mk (𝟙 (Spec (.of k)))) := by
  let family := Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 (Spec (.of k))))
    ((C.kernel J).inclusion ≫ (Over.pullback f).map i.hom.hom)
  exact family

structure ActiveAmbientComparison where
  family : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q) →
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback f).mapGrp.obj A).X (Over.mk (𝟙 (Spec (.of k))))
  realizes : ∀ J, family J = coordinateAmbientKernelFamily C i J

end AlgebraicGeometry.Isogenies.NeighborCounting.ActiveAmbientComparisonData

end

end OAI

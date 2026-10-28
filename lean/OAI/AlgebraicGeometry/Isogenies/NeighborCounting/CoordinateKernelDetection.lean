import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme

/-! # Coordinate Kernel Detection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection

/-! A constructed coordinate record and an original parameter enumeration
with its proved membership formula identify the entire generic kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {S : Scheme} {k I B : Type} [Field k]
  {f : Spec (.of k) ⟶ S} {G : Grp (Over S)} [IsCommMonObj G.X]
  {q : ℕ} [Fact q.Prime] [Module (ZMod q) (Additive (Over.mk f ⟶ G.X))]
  (C : GenericActiveCoordinateData.ActiveCoordinateData f G q) (r : ℕ)
  (e : I ≃ {J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q) // Module.finrank (ZMod q) J = r})
  (F : I → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X (Over.mk f))
  (hc : ∀ i a, C.coordinates.toAddEquiv a ∈ (e i).val ↔
    a.toMul ∈ (F i).points (Over.mk f) (𝟙 _))

include hc in
theorem coordinateKernel_membership (i : I) (a : Additive (Over.mk f ⟶ G.X)) :
    (∃ b : Over.mk (𝟙 (Spec (.of k))) ⟶ (C.kernel (e i).val).carrier,
      b ≫ (C.kernel (e i).val).inclusion = GroupPointBaseChange.pointPullbackGroupEquiv f G a.toMul) ↔
    a.toMul ∈ (F i).points (Over.mk f) (𝟙 _) :=
  (C.membership (e i).val a).symm.trans (hc i a)

variable [IsCommMonObj ((Over.pullback f).obj G.X)]
  [IsFinite ((Over.pullback f).obj G.X).hom] [Etale ((Over.pullback f).obj G.X).hom]
  (R : ∀ i, (F i).Model)
  (split : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) B ≅ (Over.pullback f).obj G.X)

include hc R split in
theorem coordinateKernel_eq_parameterSubgroup (i : I) :
    Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 (Spec (.of k)))) (C.kernel (e i).val).inclusion =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G (Over.mk f) (F i) := by
  apply SplitKernelParameterComparison.splitKernel_eq_parameterSubgroup f G split (C.kernel (e i).val) (F i) (R i)
  intro a
  exact coordinateKernel_membership C r e F hc i (Additive.ofMul a)

end AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection

namespace AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection.Split

/-! The actual finite constant splitting itself supplies all finite
etale geometry needed for detecting a coordinate kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative

theorem finite_etale_of_constantIso {S : Scheme} {B : Type} [Finite B] {H : Over S}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S B ≅ H) : IsFinite H.hom ∧ Etale H.hom := by
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  rw [← e.inv.w]
  exact ⟨inferInstance, inferInstance⟩

variable {S : Scheme} {k I B : Type} [Field k] [Finite B]
  {f : Spec (.of k) ⟶ S} {G : Grp (Over S)} [IsCommMonObj G.X]
  {q : ℕ} [Fact q.Prime] [Module (ZMod q) (Additive (Over.mk f ⟶ G.X))]
  (C : GenericActiveCoordinateData.ActiveCoordinateData f G q) (r : ℕ)
  (e : I ≃ {J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q) // Module.finrank (ZMod q) J = r})
  (F : I → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X (Over.mk f))
  (hc : ∀ i a, C.coordinates.toAddEquiv a ∈ (e i).val ↔
    a.toMul ∈ (F i).points (Over.mk f) (𝟙 _))
  (R : ∀ i, (F i).Model)
  (split : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) B ≅ (Over.pullback f).obj G.X)

include hc R split in
theorem coordinateKernel_eq_of_split (i : I) :
    Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 (Spec (.of k)))) (C.kernel (e i).val).inclusion =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G (Over.mk f) (F i) := by
  have hg := finite_etale_of_constantIso split
  let : IsFinite ((Over.pullback f).obj G.X).hom := hg.1
  let : Etale ((Over.pullback f).obj G.X).hom := hg.2
  exact coordinateKernel_eq_parameterSubgroup C r e F hc R split i

end AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection.Split

namespace AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection.Parameters

/-! Index the original parameter enumeration by its actual coordinate
record, retaining the constructed subgroup models and membership proof. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericActiveCoordinateData OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection.Split
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative

variable {S : Scheme} {k : Type} [Field k]
  {f : Spec (.of k) ⟶ S} {G : Grp (Over S)} [IsCommMonObj G.X]
  {q : ℕ} [Fact q.Prime] [Module (ZMod q) (Additive (Over.mk f ⟶ G.X))]

structure CoordinateKernelParameters (C : GenericActiveCoordinateData.ActiveCoordinateData f G q) (r : ℕ) (I : Type)
    (F : I → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X (Over.mk f)) where
  enumeration : I ≃
    {J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q) // Module.finrank (ZMod q) J = r}
  membership : ∀ i a, C.coordinates.toAddEquiv a ∈ (enumeration i).val ↔
    a.toMul ∈ (F i).points (Over.mk f) (𝟙 _)
  model : ∀ i, (F i).Model

namespace CoordinateKernelParameters

variable {C : GenericActiveCoordinateData.ActiveCoordinateData f G q} {r : ℕ} {I B : Type}
  {F : I → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X (Over.mk f)}
  (D : CoordinateKernelParameters C r I F) [Finite B]
  (split : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) B ≅ (Over.pullback f).obj G.X)

include split in
theorem kernel_eq (i : I) :
    Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 (Spec (.of k)))) (C.kernel (D.enumeration i).val).inclusion =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G (Over.mk f) (F i) :=
  Split.coordinateKernel_eq_of_split C r D.enumeration F D.membership D.model split i

end CoordinateKernelParameters

end AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection.Parameters

end

end OAI

import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedBlockKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientKernels
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberPolarizationType
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberLattices

/-! # Isogeny Quotient Cokernel Type -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientCokernelType.SphericalPELAlbaneseData

noncomputable section

/-! IsogenyQuotient's elementary divisors are the group type of the cokernel of
the actual isogeny's map on each chosen integral Tate block. All geometric
and polarization conditions come from the original IntegralModel/IsogenyQuotient inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) (h : D.RealizesIsogenyQuotient)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} (t : Local.IntegralType s)
  (x y : D.GeometricPoint b) (c : Over.mk b ⟶ (D.correspondence t).cover)
  (hs : c ≫ (D.correspondence t).source = x) (ht : c ≫ (D.correspondence t).target = y)
  (v : Fin s)

local instance : HasQuotient
    (D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b y) (v, false))
    (Submodule ℤ_[q]
      (D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b y) (v, false))) :=
  Submodule.hasQuotient (R := ℤ_[q])
    (M := D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b y) (v, false))

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46FiberTateBlockCokernelType :
    (D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b y) (v, false) ⧸
      (D.tateBlockMap hg (Over.mk (𝟙 (Spec (.of k))))
        (D.c46FiberIsogeny h t x y c hs ht) (v, false)).range) ≃+
      (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)) := by
  have := FiberLattices.charZero_of_field_spec_map b
  exact (D.tateBlockCokernelEquivKernel hg (D.c46FiberIsogeny h t x y c hs ht)
    D.reference.polarizationType (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2
    (v, false)).toAddEquiv.trans (D.c46FiberTateKernelType hg h t x y c hs ht v)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientCokernelType.SphericalPELAlbaneseData

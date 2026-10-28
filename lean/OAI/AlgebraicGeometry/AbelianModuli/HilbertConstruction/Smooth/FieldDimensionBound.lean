import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeChainStalkDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RationalStalkDimension
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Field Dimension Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldDimensionBound

noncomputable section

/-! A smooth scheme of prescribed relative dimension over an
algebraically closed field has that global dimension bound. Every
irreducible chain meets a closed rational point in its smallest member,
where the chain is bounded by the actual stalk dimension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order
universe u

theorem smoothField_topologicalKrullDim_le
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (g : ℕ) [SmoothOfRelativeDimension g p] :
    topologicalKrullDim X ≤ (g : ℕ) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth g p
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  change Order.krullDim (IrreducibleCloseds X) ≤ (g : ℕ)
  unfold Order.krullDim
  apply iSup_le
  intro C
  obtain ⟨x, hx, hclosed⟩ := nonempty_inter_closedPoints C.head.isIrreducible.nonempty
    C.head.isClosed.isLocallyClosed
  let s := pointOfClosedPoint p x hclosed
  have hs : s ≫ p = 𝟙 _ := pointOfClosedPoint_comp p x hclosed
  have hlocal : ringKrullDim (X.presheaf.stalk x) ≤ (g : ℕ) := by
    have hpt : s (IsLocalRing.closedPoint K) = x := pointOfClosedPoint_apply p x hclosed _
    exact (congrArg (fun z : X => ringKrullDim (X.presheaf.stalk z) ≤ (g : ℕ)) hpt).mp
      (RationalStalkDimension.smoothRationalPoint_stalk_krullDim_le p g s hs)
  exact (SchemeChainStalkDimension.scheme_irreducibleChain_length_le_stalkDimension X C x hx).trans hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldDimensionBound

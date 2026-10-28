import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.TransferCommon
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionClass

/-! # Common Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.CommonConcentration

noncomputable section

/-! The actual common-cover extension retains the canonical
concentration zigzag, with no change in pure degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {X : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (J : ν → X.Opens) (hJ : ∀ i, IsAffineOpen (J i))
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι V)
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ W)
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology U W J s (AdditiveCechConcentration.coefficients K) q)]
  [IsIso (RelativeCech.Refinement.homology U W J s
    (AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj (K.homology c))) q)]

include hJ in
theorem comparison :
    (AdditiveCechConcentration.iso U hU V hV K c hK q).hom ≫
      RelativeCech.CommonRefinement.comparison U V W J r s
        (AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj (K.homology c))) q =
    RelativeCech.CommonRefinement.comparison U V W J r s (AdditiveCechConcentration.coefficients K) q ≫
      (Additive.OrderedCechConcentration.iso (RelativeCech.Intersections.cover U W)
        (RelativeCech.ConcentrationNaturality.cover_affine U hU W hW) K c hK q).hom := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := QuasicoherentTruncation.cohomology K c
  let (k : ℕ) := QuasicoherentTruncation.single (K.homology c) c k
  let := CohomologyConcentration.inclusion_quasiIso K c hK
  exact TransferCommon.Comparison.comparison U hU V hV W hW J hJ r s
    (CohomologyConcentration.inclusion K c) (CohomologyConcentration.projection K c) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.CommonConcentration

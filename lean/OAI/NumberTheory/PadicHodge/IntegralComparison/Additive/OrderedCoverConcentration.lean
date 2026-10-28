import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCover

/-! # Ordered Cover Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCoverConcentration

noncomputable section

/-! The actual affine-cover comparison commutes with the canonical
pure-complex concentration. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {X : Scheme.{u}} [X.IsSeparated]
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.Opens) (V : κ → X.Opens) (W : ν → X.Opens)
  (r : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk ι U)
  (s : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ V)
  (hU : iSup U = ⊤) (hV : iSup V = ⊤) (hW : iSup W = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (haW : ∀ i, IsAffineOpen (W i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

abbrev comparison (q : ℕ) := by
  letI (k : ℕ) := QuasicoherentTruncation.truncation K c k
  letI := QuasicoherentTruncation.cohomology K c
  letI (k : ℕ) := QuasicoherentTruncation.single (K.homology c) c k
  letI := CohomologyConcentration.inclusion_quasiIso K c hK
  exact OrderedCover.Comparison.transfer U V W r s hU hV hW haU haV haW
    (CohomologyConcentration.inclusion K c) (CohomologyConcentration.projection K c) q

local instance survivor_qc : (K.homology c).IsQuasicoherent :=
  QuasicoherentTruncation.cohomology K c
local instance single_qc (q : ℕ) :
    (((single X.Modules (.up ℕ) c).obj (K.homology c)).X q).IsQuasicoherent :=
  QuasicoherentTruncation.single (K.homology c) c q

theorem square (q : ℕ) :
    (OrderedCechConcentration.iso U haU K c hK q).hom ≫
      (OrderedCover.Comparison.iso U V W r s hU hV hW haU haV haW
        ((single X.Modules (.up ℕ) c).obj (K.homology c)) q).hom =
    (OrderedCover.Comparison.iso U V W r s hU hV hW haU haV haW K q).hom ≫
      (OrderedCechConcentration.iso V haV K c hK q).hom :=
  comparison U V W r s hU hV hW haU haV haW K c hK q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCoverConcentration

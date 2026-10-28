import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureAdjunctionCoordinates

/-! # Cover Pure Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverPureMap.Reference

noncomputable section

/-! The original principal concentration and survivor adjunction map
give the same native pure-cohomology map after global cover comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (W : ι → Principal.SectionPresheaf.Index U) (f : Z ⟶ X) [IsClosedImmersion f]
  (hfU : ⊤ ≤ f ⁻¹ᵁ U)
  (J : ν → X.Opens) (hJ : ∀ i, IsAffineOpen (J i))
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (Principal.RelativeConcentration.family U hU W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk
    (ComplementaryAffineCover.Index (SectionIdealPuncturedCover.outside f.ker))
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)))
  (V : κ → X.Opens) (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (N : X.Modules) [N.IsQuasicoherent] (φ : K.homology c ⟶ N) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients K) q)]
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients
      ((single X.Modules (.up ℕ) c).obj (K.homology c))) q)]
  [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
    (Relative.AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj N)) q)]

local instance survivor_qc : (K.homology c).IsQuasicoherent :=
  QuasicoherentTruncation.cohomology K c
local instance single_qc (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    (((single X.Modules (.up ℕ) c).obj M).X q).IsQuasicoherent :=
  QuasicoherentTruncation.single M c q

include hJ in
theorem comparison :
    (Principal.AdditiveSections.forgetScalars U).map
      ((Concentration.Reference.iso U hU W K c hK q).hom ≫
        (Concentration.Reference.functor U hU W q).map
          ((single X.Modules (.up ℕ) c).map φ)) ≫
      CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV
        (K := (single X.Modules (.up ℕ) c).obj N) q ≫
      (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
        ((single X.Modules (.up ℕ) c).obj N) q).inv =
    CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV (K := K) q ≫
      (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π V q K).inv ≫
      (Global.PureIntrinsicCoordinates.Intrinsic.concentration π V haV K c hK q).hom ≫
      (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)).map
        (homologyMap ((Cech.ConcentrationNaturality.totalFunctor π V).map
          ((single X.Modules (.up ℕ) c).map φ)) q) := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((Principal.AdditiveSections.forgetScalars U).map
      ((Concentration.Reference.functor U hU W q).map
        ((single X.Modules (.up ℕ) c).map φ))),
    CoverNaturality.Reference.comparison U hU W f hfU J r s V hV haV
      ((single X.Modules (.up ℕ) c).map φ) q]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((Principal.AdditiveSections.forgetScalars U).map
      (Concentration.Reference.iso U hU W K c hK q).hom),
    CoverConcentration.Reference.comparison U hU W f hfU J hJ r s V hV haV K c hK q]
  simpa only [Category.assoc] using congrArg
    (CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV (K := K) q ≫ ·)
      (Global.PureAdjunctionCoordinates.comparison π V haV K c hK N φ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverPureMap.Reference

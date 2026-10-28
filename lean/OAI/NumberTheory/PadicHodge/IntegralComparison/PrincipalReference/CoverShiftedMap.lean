import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverPureMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIndexedCoordinates

/-! # Cover Shifted Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverShiftedMap.Reference

noncomputable section

/-! The original principal-to-global comparison followed by the signed
single-row identification recovers the original shifted pure class. -/
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
  (N : X.Modules) [N.IsQuasicoherent] (φ : K.homology c ⟶ N)
  (g q : ℕ) (hq : q=g+c)
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
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)
local instance single_qc (M : X.Modules) [M.IsQuasicoherent] (k : ℕ) :
    (((single X.Modules (.up ℕ) c).obj M).X k).IsQuasicoherent :=
  QuasicoherentTruncation.single M c k

include hJ in
theorem comparison :
    (Principal.AdditiveSections.forgetScalars U).map
      ((Concentration.Reference.iso U hU W K c hK q).hom ≫
        (Concentration.Reference.functor U hU W q).map
          ((single X.Modules (.up ℕ) c).map φ)) ≫
      CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV
        (K := (single X.Modules (.up ℕ) c).obj N) q ≫
      (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
        ((single X.Modules (.up ℕ) c).obj N) q).inv ≫
      (Global.PureIndexedCoordinates.singleIso π V N c g q hq).hom =
    CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV (K := K) q ≫
      (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π V q K).inv ≫
      (Global.PureIndexedCoordinates.concentration π V haV K c hK g q hq).hom ≫
      (G).map (homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π V).map φ) g) := by
  have h := congrArg (fun z => z ≫
    (Global.PureIndexedCoordinates.singleIso π V N c g q hq).hom)
    (CoverPureMap.Reference.comparison π U hU W f hfU J hJ r s V hV haV K c hK N φ q)
  simp only [Category.assoc] at h
  rw [Global.PureIndexedCoordinates.map_single π V haV K c hK N φ g q hq] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.CoverShiftedMap.Reference

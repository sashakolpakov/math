import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SingleCoordinates

/-! # Single Base Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SingleBaseCoordinates.Reference

noncomputable section

/-! The original principal single-class comparison with the actual
base morphism used by projective Serre cohomology. The change of base
retains the same unshifted presheaf comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (W : ι → Principal.SectionPresheaf.Index U) (f : Z ⟶ X) [IsClosedImmersion f] (hfU : ⊤ ≤ f ⁻¹ᵁ U)
  (J : ν → X.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (Principal.RelativeConcentration.family U hU W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk
    (ComplementaryAffineCover.Index (SectionIdealPuncturedCover.outside f.ker))
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)))
  (V : κ → X.Opens) (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
  (N : X.Modules) [N.IsQuasicoherent] (c g q : ℕ) (hq : q=g+c)

local instance single_qc (k : ℕ) :
    ((Reference.SinglePresheafCoordinates.moduleSingle N c).X k).IsQuasicoherent :=
  QuasicoherentTruncation.single N c k

variable [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
  (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)) J s
  (Relative.AdditiveCechConcentration.coefficients
    (Reference.SinglePresheafCoordinates.moduleSingle N c)) q)]

def coefficientComparison :=
  SingleCoordinates.Reference.coefficientComparison
    U hU W f hfU J r s V hV haV N c g q hq ≫
    (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso (𝟙 X) V N g).hom ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso π V N g).inv

omit [X.IsSeparated] [N.IsQuasicoherent] in
private theorem output_change :
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso (𝟙 X) V
      (Reference.SinglePresheafCoordinates.moduleSingle N c) q).inv ≫
      (Global.PureIndexedCoordinates.singleIso (𝟙 X) V N c g q hq).hom ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso (𝟙 X) V N g).hom ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso π V N g).inv =
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
      (Reference.SinglePresheafCoordinates.moduleSingle N c) q).inv ≫
      (Global.PureIndexedCoordinates.singleIso π V N c g q hq).hom := by
  rw [← Reference.SingleGlobalCoordinates.inverse π V N c g q hq]
  rw [← Category.assoc _
    (Global.PureIndexedCoordinates.singleIso (𝟙 X) V N c g q hq).hom]
  rw [← Reference.SingleGlobalCoordinates.inverse (𝟙 X) V N c g q hq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem comparison :
    CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV
      (K := Reference.SinglePresheafCoordinates.moduleSingle N c) q ≫
      (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
        (Reference.SinglePresheafCoordinates.moduleSingle N c) q).inv ≫
      (Global.PureIndexedCoordinates.singleIso π V N c g q hq).hom =
    (Principal.SinglePresheafCoordinates.coordinates U hU N c W g q hq).hom ≫
      coefficientComparison π U hU W f hfU J r s V hV haV N c g q hq := by
  have h := congrArg (fun a => a ≫
    (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso (𝟙 X) V N g).hom ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso π V N g).inv)
    (SingleCoordinates.Reference.comparison U hU W f hfU J r s V hV haV N c g q hq)
  simp only [Category.assoc] at h
  rw [output_change π V N c g q hq] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SingleBaseCoordinates.Reference

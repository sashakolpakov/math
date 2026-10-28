import OAI.RepresentationTheory.Theta.Geometric.Picard.StalkParameters
import OAI.RepresentationTheory.Theta.Geometric.StandardChartPicardFlatness
import OAI.RepresentationTheory.Theta.Geometric.StalkChartProjection
import OAI.RepresentationTheory.Theta.Geometric.FlatSourceLocalizations

/-! # Stalk Flatness -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.StalkFlatness

noncomputable section

/-! The actual Picard comparison projection is flat after localization
at a comparison point when its fiber H1 fits the smooth ambient dimension. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {A B : Over (Spec (.of K))}
    [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian B.left] (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)
    {Y : Scheme.{u}} (n : ℕ) (p : B.left ⟶ Y) [SmoothOfRelativeDimension n p]
    [Mono (D.zeroScheme.hom ≫ p)] (z : D.zeroScheme.left)

theorem picard_zeroScheme_stalk_projection_flat
    (hdim : Projective.PicardLocalEquations.projectiveClosedFiberH1
      (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (StalkParameters.picardStalkParameter B (D.zeroScheme.hom z))).hom
      (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A (StalkParameters.picardStalkParameter B (D.zeroScheme.hom z)))
      (D.line (StalkParameters.picardStalkMap B (D.zeroScheme.hom z))) ≤ n) :
    Flat (pullback.fst D.zeroScheme.hom (B.left.fromSpecStalk (D.zeroScheme.hom z)) ≫
      D.zeroScheme.hom ≫ p) := by
  let b := D.zeroScheme.hom z
  let j := B.left.fromSpecStalk b
  obtain ⟨U, hU, V, hV, hb, hv, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) b
  let : Algebra Γ(Y, U) Γ(B.left, V) := (p.appLE U V hv).hom.toAlgebra
  let := TopCat.Presheaf.algebra_section_stalk B.left.presheaf (⟨b, hb⟩ : V)
  let : Algebra Γ(Y, U) (B.left.presheaf.stalk b) :=
    ((B.left.presheaf.germ V b hb).hom.comp (p.appLE U V hv).hom).toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(B.left, V) (B.left.presheaf.stalk b) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) Γ(B.left, V) := hstd
  have : IsLocalization.AtPrime (B.left.presheaf.stalk b) (hV.primeIdealOf ⟨b, hb⟩).asIdeal :=
    hV.isLocalization_stalk ⟨b, hb⟩
  let r := Spec.map (p.appLE U V hv ≫ B.left.presheaf.germ V b hb)
  let q := pullback.snd D.zeroScheme.hom j ≫ r
  have hfac : q ≫ hU.fromSpec = pullback.fst D.zeroScheme.hom j ≫ D.zeroScheme.hom ≫ p := by
    rw [show q = pullback.snd D.zeroScheme.hom j ≫ r from rfl, Category.assoc,
      show r ≫ hU.fromSpec = j ≫ p from StalkChartProjection.stalkChart_projection p b hU hV hb hv,
      ← Category.assoc, ← pullback.condition, Category.assoc]
  have : Mono (q ≫ hU.fromSpec) := hfac.symm ▸ inferInstance
  have : Mono q := mono_of_mono q hU.fromSpec
  have : FormallyUnramified q := inferInstance
  have : FormallyUnramified
      ((SubobjectPullbackPoints.subobjectPullback D.zeroScheme (StalkParameters.picardStalkMap B b).left).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (B.left.presheaf.stalk b)))) := by
    change FormallyUnramified q
    infer_instance
  obtain ⟨eM⟩ := StalkParameters.picardStalk_fiber_trivial D z
  have hflat : Flat q := StandardChartPicardFlatness.picard_standardLocalization_flat
    (R := Γ(Y, U)) (P := Γ(B.left, V)) (S := B.left.presheaf.stalk b)
    (W := (hV.primeIdealOf ⟨b, hb⟩).asIdeal.primeCompl) (n := n)
    (D := D) (γ := j ≫ B.hom) (a := StalkParameters.picardStalkMap B b) eM hdim
  have : Flat (q ≫ hU.fromSpec) := inferInstance
  rwa [hfac] at this

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.StalkFlatness

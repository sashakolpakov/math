import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkParameters
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStandardFlatness
import OAI.RepresentationTheory.Theta.Geometric.StalkChartProjection
import OAI.RepresentationTheory.Theta.Geometric.FlatSourceLocalizations

/-! # Relative Stalk Flatness -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkFlatness.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! The actual Picard comparison projection is flat after localization
at a comparison point when its fiber H1 fits the smooth ambient dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem stalkChart_baseChange_projection {X Y Z : Scheme}
    (f : Z ⟶ X) (p : X ⟶ Y) (b : X)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hb : b ∈ V) (hv : V ≤ p ⁻¹ᵁ U) :
    (pullback.snd f (X.fromSpecStalk b) ≫ Spec.map (p.appLE U V hv ≫ X.presheaf.germ V b hb)) ≫
      hU.fromSpec = pullback.fst f (X.fromSpecStalk b) ≫ f ≫ p := by
  let j := X.fromSpecStalk b
  let r := Spec.map (p.appLE U V hv ≫ X.presheaf.germ V b hb)
  have hr : r ≫ hU.fromSpec = j ≫ p := RepresentationTheory.Theta.Geometric.StalkChartProjection.stalkChart_projection p b hU hV hb hv
  calc
    (pullback.snd f j ≫ r) ≫ hU.fromSpec = pullback.snd f j ≫ (r ≫ hU.fromSpec) :=
      Category.assoc _ _ _
    _ = pullback.snd f j ≫ (j ≫ p) := congrArg (fun k => pullback.snd f j ≫ k) hr
    _ = (pullback.snd f j ≫ j) ≫ p := (Category.assoc _ _ _).symm
    _ = (pullback.fst f j ≫ f) ≫ p :=
      congrArg (fun k => k ≫ p) (pullback.condition (f := f) (g := j)).symm
    _ = pullback.fst f j ≫ f ≫ p := Category.assoc _ _ _

theorem stalkChart_baseChange_unramified {X Y Z : Scheme}
    (f : Z ⟶ X) (p : X ⟶ Y) [FormallyUnramified (f ≫ p)] (b : X)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hb : b ∈ V) (hv : V ≤ p ⁻¹ᵁ U) :
    FormallyUnramified (pullback.snd f (X.fromSpecStalk b) ≫
      Spec.map (p.appLE U V hv ≫ X.presheaf.germ V b hb)) := by
  let q := pullback.snd f (X.fromSpecStalk b) ≫
    Spec.map (p.appLE U V hv ≫ X.presheaf.germ V b hb)
  have hcomp : FormallyUnramified (q ≫ hU.fromSpec) :=
    (congrArg FormallyUnramified (stalkChart_baseChange_projection f p b hU hV hb hv)).mpr
      (MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance
        (inferInstanceAs (FormallyUnramified (f ≫ p))))
  let := hcomp
  exact FormallyUnramified.of_comp q hU.fromSpec

variable {S : Scheme} {A B : Over S}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (PP : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    {Y : Scheme} (n : ℕ) (p : B.left ⟶ Y) [SmoothOfRelativeDimension n p]
    [FormallyUnramified ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom ≫ p)] (z : (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).left)

omit [SmoothOfRelativeDimension n p] in
theorem stalkChart_zeroScheme_flat
    {U : Y.Opens} (hU : IsAffineOpen U) {V : B.left.Opens} (hV : IsAffineOpen V)
    (hb : (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z ∈ V) (hv : V ≤ p ⁻¹ᵁ U)
    (hstd : letI : Algebra Γ(Y, U) Γ(B.left, V) := (p.appLE U V hv).hom.toAlgebra
      Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) Γ(B.left, V))
    (hdim : RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z))).hom
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z)) PP)
      (D.line (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkMap B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z))) ≤ n) :
    Flat (pullback.snd (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom (B.left.fromSpecStalk ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z)) ≫
      Spec.map (p.appLE U V hv ≫ B.left.presheaf.germ V ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z) hb)) := by
  let b := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z
  let hlocal : IsLocalRing (B.left.presheaf.stalk b) :=
    B.left.toLocallyRingedSpace.isLocalRing b
  let j := B.left.fromSpecStalk b
  let : Algebra Γ(Y, U) Γ(B.left, V) := (p.appLE U V hv).hom.toAlgebra
  let := TopCat.Presheaf.algebra_section_stalk B.left.presheaf (⟨b, hb⟩ : V)
  let : Algebra Γ(Y, U) (B.left.presheaf.stalk b) :=
    ((B.left.presheaf.germ V b hb).hom.comp (p.appLE U V hv).hom).toAlgebra
  let : IsScalarTower Γ(Y, U) Γ(B.left, V) (B.left.presheaf.stalk b) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime (B.left.presheaf.stalk b) (hV.primeIdealOf ⟨b, hb⟩).asIdeal :=
    hV.isLocalization_stalk ⟨b, hb⟩
  let r := Spec.map (p.appLE U V hv ≫ B.left.presheaf.germ V b hb)
  let q := pullback.snd (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom j ≫ r
  let : FormallyUnramified q :=
    stalkChart_baseChange_unramified (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom p b hU hV hb hv
  have hunramified : FormallyUnramified
      ((RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP) (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkMap B b).left).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (B.left.presheaf.stalk b)))) := by
    change FormallyUnramified q
    infer_instance
  obtain ⟨eM⟩ := RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalk_fiber_trivial PP D z
  exact @RelativeStandardFlatness.Geometric.RelativeRigidifiedCharts.standardLocalization_flat
    Γ(Y, U) Γ(B.left, V) (B.left.presheaf.stalk b)
    _ _ _ hlocal _ _ _ _ _
    (hV.primeIdealOf ⟨b, hb⟩).asIdeal.primeCompl _ n hstd
    S A B _ _ _ _ _ PP D (j ≫ B.hom) (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkMap B b) hunramified eM hdim

theorem stalk_projection_flat
    (hdim : RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z))).hom
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z)) PP)
      (D.line (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkMap B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z))) ≤ n) :
    Flat (pullback.fst (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom (B.left.fromSpecStalk ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z)) ≫
      (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom ≫ p) := by
  let b := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom z
  obtain ⟨U, hU, V, hV, hb, hv, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) b
  let q := pullback.snd (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom (B.left.fromSpecStalk b) ≫
    Spec.map (p.appLE U V hv ≫ B.left.presheaf.germ V b hb)
  let : Flat q := stalkChart_zeroScheme_flat PP D n p z hU hV hb hv hstd hdim
  have hflat : Flat (q ≫ hU.fromSpec) := inferInstance
  have hfac := stalkChart_baseChange_projection (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP).hom p b hU hV hb hv
  change q ≫ hU.fromSpec = _ at hfac
  rwa [hfac] at hflat

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkFlatness.Geometric.RelativeRigidifiedCharts

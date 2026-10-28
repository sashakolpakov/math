import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalFlatness
import OAI.RepresentationTheory.Theta.Geometric.SpecLocalizationProperties
import OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings

/-! # Relative Standard Flatness -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStandardFlatness.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! A standard smooth chart and its actual localization supply every
ambient algebra hypothesis for flatness of the local Picard projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory KaehlerDifferential

variable {R P S : Type}
    [CommRing R] [CommRing P] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]
    (W : Submonoid P) [IsLocalization W S]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R P]

local instance : IsLocalRing Γ(Spec (.of S), ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isLocalRing S
local instance : IsNoetherianRing Γ(Spec (.of S), ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isNoetherianRing S

variable {Base : Scheme} {A B : Over Base} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (PP : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    (γ : Spec (.of S) ⟶ Base) (a : Over.mk γ ⟶ B)

local instance : IsAffine (Over.mk γ).left := inferInstanceAs (IsAffine (Spec (.of S)))
local instance : IsLocalRing Γ((Over.mk γ).left, ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isLocalRing S
local instance : IsNoetherianRing Γ((Over.mk γ).left, ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isNoetherianRing S

local instance : IsLocallyNoetherian (Over.mk γ).left :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of S)))

include W PP in
theorem standardLocalization_flat
    [FormallyUnramified ((RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP) a.left).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (eM : (Scheme.Modules.pullback ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (Over.mk γ)).hom.fiberι
      (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint (Spec (.of S))))).obj (D.line a).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (Over.mk γ)).hom.fiber
        (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint (Spec (.of S)))))
    (hdim : RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1 (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (Over.mk γ)).hom
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A (Over.mk γ) PP) (D.line a) ≤ n) :
    Flat ((RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP) a.left).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let := RepresentationTheory.Theta.Geometric.SpecLocalizationProperties.specGlobalAlgebra R S
  obtain ⟨hsm, hflat, hfree, hfinite, hrank⟩ :=
    RepresentationTheory.Theta.Geometric.SpecLocalizationProperties.standardSmooth_spec_localization_properties (R := R) (P := P) (S := S) W n
  have := hsm
  have := hflat
  have := hfree
  have := hfinite
  have h :
      letI : Algebra R Γ(Spec (.of S), ⊤) :=
        (FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv (Spec (.of S)) (.of R)
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).toAlgebra
      ∀ [Algebra.FormallySmooth R Γ(Spec (.of S), ⊤)]
        [Module.Flat R Γ(Spec (.of S), ⊤)]
        [Module.Free Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R]]
        [Module.Finite Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R]],
        RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1 (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (Over.mk γ)).hom
          (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A (Over.mk γ) PP) (D.line a) ≤
          Module.finrank Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R] →
        Flat ((RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D PP) a.left).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    @RelativeLocalFlatness.Geometric.RelativeRigidifiedCharts.zeroScheme_local_toSpec_flat Base A B (Over.mk γ) _ _ _ _ _ PP D _ _ _ _ a R _
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) _ eM
  rw [RepresentationTheory.Theta.Geometric.SpecLocalizationProperties.specGlobalAlgebra_pointMap] at h
  exact @h hsm hflat hfree hfinite (hdim.trans hrank.symm.le)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStandardFlatness.Geometric.RelativeRigidifiedCharts

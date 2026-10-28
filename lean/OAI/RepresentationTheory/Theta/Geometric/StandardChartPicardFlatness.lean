import OAI.RepresentationTheory.Theta.Geometric.Picard.LocalFlatnessOverRing
import OAI.RepresentationTheory.Theta.Geometric.SpecLocalizationProperties
import OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings

/-! # Standard Chart Picard Flatness -/

namespace OAI.RepresentationTheory.Theta.Geometric.StandardChartPicardFlatness

noncomputable section

/-! A standard smooth chart and its actual localization supply every
ambient algebra hypothesis for flatness of the local Picard projection. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory KaehlerDifferential

universe u
variable {K R P S : Type u} [Field K] [IsAlgClosed K]
    [CommRing R] [CommRing P] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]
    (W : Submonoid P) [IsLocalization W S]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R P]

local instance : IsLocalRing Γ(Spec (.of S), ⊤) := SpecLocalRings.specGlobal_isLocalRing S
local instance : IsNoetherianRing Γ(Spec (.of S), ⊤) := SpecLocalRings.specGlobal_isNoetherianRing S

variable {A B : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian B.left] (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)
    (γ : Spec (.of S) ⟶ Spec (.of K)) (a : Over.mk γ ⟶ B)

local instance : IsAffine (Over.mk γ).left := inferInstanceAs (IsAffine (Spec (.of S)))
local instance : IsLocalRing Γ((Over.mk γ).left, ⊤) := SpecLocalRings.specGlobal_isLocalRing S
local instance : IsNoetherianRing Γ((Over.mk γ).left, ⊤) := SpecLocalRings.specGlobal_isNoetherianRing S

include W in
theorem picard_standardLocalization_flat
    [FormallyUnramified ((SubobjectPullbackPoints.subobjectPullback D.zeroScheme a.left).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (eM : (Scheme.Modules.pullback ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (Over.mk γ)).hom.fiberι
      (Local.AxisCechChart.affineLocalClosedPoint (Spec (.of S))))).obj (D.line a).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (Over.mk γ)).hom.fiber
        (Local.AxisCechChart.affineLocalClosedPoint (Spec (.of S)))))
    (hdim : Projective.PicardLocalEquations.projectiveClosedFiberH1 (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (Over.mk γ)).hom
      (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A (Over.mk γ)) (D.line a) ≤ n) :
    Flat ((SubobjectPullbackPoints.subobjectPullback D.zeroScheme a.left).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let := SpecLocalizationProperties.specGlobalAlgebra R S
  obtain ⟨hsm, hflat, hfree, hfinite, hrank⟩ :=
    SpecLocalizationProperties.standardSmooth_spec_localization_properties (R := R) (P := P) (S := S) W n
  have := hsm
  have := hflat
  have := hfree
  have := hfinite
  have h :
      letI : Algebra R Γ(Spec (.of S), ⊤) :=
        (AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv (Spec (.of S)) (.of R)
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).toAlgebra
      ∀ [Algebra.FormallySmooth R Γ(Spec (.of S), ⊤)]
        [Module.Flat R Γ(Spec (.of S), ⊤)]
        [Module.Free Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R]]
        [Module.Finite Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R]],
        Projective.PicardLocalEquations.projectiveClosedFiberH1 (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (Over.mk γ)).hom
          (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A (Over.mk γ)) (D.line a) ≤
          Module.finrank Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R] →
        Flat ((SubobjectPullbackPoints.subobjectPullback D.zeroScheme a.left).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    @Picard.LocalFlatnessOverRing.picard_zeroScheme_local_toSpec_flat K _ _ A B (Over.mk γ) _ _ _ _ _ _ D
      _ _ _ a R _ (Spec.map (CommRingCat.ofHom (algebraMap R S))) _ eM
  rw [SpecLocalizationProperties.specGlobalAlgebra_pointMap] at h
  exact @h hsm hflat hfree hfinite (hdim.trans hrank.symm.le)

end

end OAI.RepresentationTheory.Theta.Geometric.StandardChartPicardFlatness

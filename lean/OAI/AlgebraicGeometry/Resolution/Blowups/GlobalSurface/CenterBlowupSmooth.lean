import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.CenterBlowupSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupSmoothEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CenterSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalSurfaceCenter

/-! # Center Blowup Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The canonical surface center has a smooth actual global blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_blowup_smooth (ℓ : ℕ)
    (C : ∀ i, Surface.TangentCenterChoice.Construction.SurfaceTangentCenterChoice ℂ (A.rings i) (A.ideals i) n ℓ)
    (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hres : ∀ i, I.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (C i).center)
    (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2) :
    Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := by
  apply Global.CenterSmooth.Construction.globalBlowup_smooth_of_affine_cover I hI f A.nativeOpens A.nativeOpens_cover
  intro i
  let : Algebra ℂ Γ(X, A.nativeOpens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.nativeOpens i)
  rw [← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (A.nativeOpens i), A.surfaceCenter_ideal ℓ C I hres i]
  let e := Affine.OpenBoundaryTransport.Construction.specOpenSectionAlgEquiv f (A.rings i) (A.map i) (A.ground i)
  let : Smooth (ReesGrading.Construction.affineBlowupToSpec (C i).center ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (A.rings i)))) := (C i).blowup_smooth (hdim i)
  exact Affine.BlowupSmoothEquiv.Construction.affineBlowup_smooth_of_comap_algEquiv e (C i).center

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_isBlowupSmooth (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1))
    (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase (A.surfaceCenter ℓ hb hdim hlevel)
      (A.surfaceCenter_nonzero ℓ hb hdim hlevel) ≫ f) :=
  A.surfaceCenter_blowup_smooth ℓ _ _ _ (A.surfaceCenter_restrict ℓ hb hdim hlevel) hdim

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.canonicalSurfaceCenter_blowup_smooth [CompactSpace X] [Smooth f]
    (hc : A.center = ⊤) (hn : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n ≠ ⊤)
    (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2) :
    Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase (A.canonicalSurfaceCenter hc hn hdim)
      (A.canonicalSurfaceCenter_nonzero hc hn hdim) ≫ f) :=
  A.surfaceCenter_isBlowupSmooth (A.coefficientBound hc - 1)
    (A.canonicalSurface_bound hc hn) hdim (A.canonicalSurface_level hc hn)

end

end OAI.AlgebraicGeometry.Resolution.Blowups

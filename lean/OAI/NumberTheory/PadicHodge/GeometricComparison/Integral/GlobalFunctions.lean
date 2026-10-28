import OAI.NumberTheory.PadicHodge.GeometricComparison.Integrality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSplitMap

/-! # Global Functions -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalFunctions.IntegralGlobalFunctions

noncomputable section

/-! Actual global functions of an abelian scheme over an integral noetherian affine base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

theorem appTop_isIso {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R))) :
    IsIso A.scheme.hom.appTop := by
  let : GeometricallyIntegral A.scheme.hom :=
    Integrality.GeometricIntegrality.of_smooth_geometricallyConnected A.scheme.hom
  let : IsIntegral A.scheme.left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.scheme.hom
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply AlgebraicGeometry.FormalGeometry.Completion.IntegralSplitMap.Construction.integral_split_bijective A.scheme.hom.appTop.hom (η[A.scheme]).left.appTop.hom
    (isIntegral_appTop_of_universallyClosed A.scheme.hom)
  have h : A.scheme.hom.appTop ≫ (η[A.scheme]).left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, (η[A.scheme]).w]
    rfl
  exact congrArg CommRingCat.Hom.hom h

theorem spec_appTop_surjective {R S : Type u} [CommRing R] [CommRing S]
    (r : R →+* S) (hr : Function.Surjective r) :
    Function.Surjective (Spec.map (CommRingCat.ofHom r)).appTop.hom := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r)
  have hs : Function.Surjective
      (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom r)).appTop).hom) := by
    rw [← h]
    exact ((Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv.symm.surjective).comp hr
  change Function.Surjective ((Spec.map (CommRingCat.ofHom r)).appTop.hom ∘
    (Scheme.ΓSpecIso (.of R)).inv.hom) at hs
  exact hs.of_comp

theorem baseChange_surjective {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S]
    {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R)))
    (r : R →+* S) (hr : Function.Surjective r) :
    Function.Surjective (pullback.fst A.scheme.hom (Spec.map (CommRingCat.ofHom r))).appTop.hom := by
  let b := Spec.map (CommRingCat.ofHom r)
  let B := A.pullback b
  let : IsIso B.scheme.hom.appTop := appTop_isIso B
  have hB : Function.Surjective B.scheme.hom.appTop.hom :=
    (ConcreteCategory.isIso_iff_bijective B.scheme.hom.appTop).mp inferInstance |>.surjective
  have h := congrArg Scheme.Hom.appTop (pullback.condition (f := A.scheme.hom) (g := b))
  simp only [Scheme.Hom.comp_appTop] at h
  have hs : Function.Surjective
      ((A.scheme.hom.appTop ≫ (pullback.fst A.scheme.hom b).appTop).hom) := by
    rw [h]
    exact hB.comp (spec_appTop_surjective r hr)
  change Function.Surjective ((pullback.fst A.scheme.hom b).appTop.hom ∘
    A.scheme.hom.appTop.hom) at hs
  exact hs.of_comp

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalFunctions.IntegralGlobalFunctions

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.MorphismPropertyOpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomOpenLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.ParameterPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationPositiveTransport
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Open Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Original polarizations descend on an open cover once their actual
maps glue. Finite-flat degree and geometric kernel groups are both
retained, and positivity uses the original ample fiber witnesses. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S : Scheme.{u}} {g : ℕ}

section

theorem Abelian.Schemes.AbelianScheme.Isogeny.hasPolarizationType_of_openCover
    {A B : Abelian.Schemes.AbelianScheme g S} (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (δ : Fin g → ℕ)
    (C : S.OpenCover.{u}) (h : ∀ i, (p.pullback (C.f i)).HasPolarizationType δ) :
    p.HasPolarizationType δ where
  degree b := by
    obtain ⟨i, x, hx⟩ := C.exists_eq (B.scheme.hom b)
    obtain ⟨z, hzb, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := B.scheme.hom) (g := C.f i) b x hx.symm
    have hr := Scheme.Hom.finrank_of_isPullback _ _ _ _
      (Projective.PresentationBaseChange.overPullback_map_isPullback p.hom (C.f i)) z
    exact (congrArg p.hom.left.finrank hzb).symm.trans (hr.symm.trans ((h i).degree z))
  geometricKernel K _ _ s := by
    obtain ⟨i, x, hx⟩ := C.exists_eq (s default)
    obtain ⟨a, ha, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (C.f i) s x hx
    subst s
    exact ⟨(p.kernelBaseChangeEquiv (C.f i) (Over.mk a)).symm.trans
      ((h i).geometricKernel K a).some⟩

end

theorem Polarization.OpenDescent.positiveOnGeometricFibers_of_openCover
    {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (C : S.OpenCover.{u})
    (h : ∀ i, ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ C.X i),
      PolarizationData.PositiveOnGeometricFiber (D.pullback (C.f i)) ((Over.pullback (C.f i)).map p) K s)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    PolarizationData.PositiveOnGeometricFiber D p K s := by
  obtain ⟨i, x, hx⟩ := C.exists_eq (s default)
  obtain ⟨a, ha, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (C.f i) s x hx
  have hp := PELModuli.IntegralModel.PolarizationPositiveTransport.positiveOnGeometricFiber_of_pullback D p (C.f i) a (h i K a)
  exact ha ▸ hp

def Polarization.OpenDescent.polarizationOfOpenCover
    {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A) (δ : Fin g → ℕ)
    (p : A.scheme ⟶ D.abelian.scheme) (C : S.OpenCover.{u})
    (q : ∀ i, PolarizationData.Polarization (D.pullback (C.f i)) δ)
    (hq : ∀ i, (Over.pullback (C.f i)).map p = (q i).isogeny.hom) :
    PolarizationData.Polarization D δ := by
  let : IsMonHom p := MonoidHomOpenLocality.isMonHom_of_openCover p C (fun i =>
    (hq i).symm ▸ (q i).isogeny.preservesGroup)
  let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  let : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat) (Q := RingHom.Flat)
  let hf : IsFinite p.left := HilbertConstruction.Over.MorphismPropertyOpenDescent.overMorphism_property_of_openCover p C (@IsFinite)
    (fun i => (congrArg Over.Hom.left (hq i)).symm ▸ (q i).isogeny.finite)
  let hfl : Flat p.left := HilbertConstruction.Over.MorphismPropertyOpenDescent.overMorphism_property_of_openCover p C (@Flat)
    (fun i => (congrArg Over.Hom.left (hq i)).symm ▸ (q i).isogeny.flat)
  let hs : Surjective p.left := HilbertConstruction.Over.MorphismPropertyOpenDescent.overMorphism_property_of_openCover p C (@Surjective)
    (fun i => (congrArg Over.Hom.left (hq i)).symm ▸ (q i).isogeny.surjective)
  let m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian := ⟨p, inferInstance, hf, hfl, hs⟩
  refine ⟨m, m.hasPolarizationType_of_openCover δ C ?_, ?_⟩
  · intro i
    have he : m.pullback (C.f i) = (q i).isogeny := Isogeny.ParameterPullback.isogeny_eq_of_hom_eq (hq i)
    exact he.symm ▸ (q i).kernelType
  · exact Polarization.OpenDescent.positiveOnGeometricFibers_of_openCover D p C (fun i K _ _ s =>
      (hq i).symm ▸ (q i).positive K s)

theorem Polarization.OpenDescent.polarizationOfOpenCover_hom
    {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A) (δ : Fin g → ℕ)
    (p : A.scheme ⟶ D.abelian.scheme) (C : S.OpenCover.{u})
    (q : ∀ i, PolarizationData.Polarization (D.pullback (C.f i)) δ)
    (hq : ∀ i, (Over.pullback (C.f i)).map p = (q i).isogeny.hom) :
    (Polarization.OpenDescent.polarizationOfOpenCover D δ p C q hq).isogeny.hom = p := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

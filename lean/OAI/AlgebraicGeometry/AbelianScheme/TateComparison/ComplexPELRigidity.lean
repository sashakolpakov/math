import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicLevelRigidity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationPeriodSimilitude
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport

/-! # Complex PEL Rigidity -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianScheme.TateComparison.ComplexPELRigidity

/-! Full-level rigidity for an actual polarized complex abelian scheme,
using its homology polarization identity and the native Chern form. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem nativeEndomorphism_injective {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) :
    Function.Injective (AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P) := by
  intro f h he
  have hh := congrArg (fun k => (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).inv ≫ k ≫ (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom) he
  simpa only [AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using hh

theorem polarized_abelian_eq_id {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : A.abelian.scheme ≅ A.abelian.scheme) [IsMonHom e.hom] (hN : 3 ≤ N)
    (hhom : ∀ x y, AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing A
      (HomologicalComplex.homologyMap
        ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map
          (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous e.hom))) 1 x)
      (HomologicalComplex.homologyMap
        ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map
          (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous e.hom))) 1 y) =
      1 • AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing A x y)
    (hlevel : AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.PreservesFullLevel A.level e.hom) : e.hom = 𝟙 A.abelian.scheme := by
  let J := AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let B := AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian J
  let en := AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphismIso A.abelian J e
  have : IsMonHom en.hom := inferInstanceAs (IsMonHom (AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A.abelian J e.hom))
  have : NeZero N := ⟨by omega⟩
  have hperiod : ∀ x y : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm B (AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle A) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift en.hom x) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift en.hom y) =
        AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm B (AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle A) x y := by
    intro x y
    have hp := PolarizationPeriodSimilitude.polarizationPeriod_map_similitude (n := 1) A A e.hom hhom x y
    simp only [one_nsmul] at hp
    exact hp
  have hcong := (AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.preservesFullLevel_iff_native_congruence A.abelian J A.level e.hom).mp hlevel
  have he : en.hom = 𝟙 B.toOver :=
    IntrinsicLevelRigidity.nativeChern_period_congruence_rigidity B (AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle A)
      (AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle_ample A) en hperiod N hN hcong
  apply nativeEndomorphism_injective A.abelian J
  exact he.trans (AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism_id A.abelian J).symm

end AlgebraicGeometry.AbelianScheme.TateComparison.ComplexPELRigidity

namespace AlgebraicGeometry.AbelianScheme.TateComparison

/-! A full marked polarized PEL automorphism over the complex field is
the identity on the actual abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {R : Type} [CommRing R] {g N : ℕ} {δ : Fin g → ℕ}
  {P : PEL.PELFamilyData R g N Foundations.Scheme.ProjectiveSpace.complexBase} {c : R →+* R}

theorem PELModuli.PELFamilyIso.complex_abelian_eq_id (e : PELModuli.PELFamilyIso P P) (hP : P.IsPEL δ c) (hN : 3 ≤ N) :
    e.abelian.hom = 𝟙 P.abelian.scheme :=
  ComplexPELRigidity.polarized_abelian_eq_id (P.toPolarized hP) e.abelian hN
    (e.toIsogeny.polarizationHomology_similitude hP hP) e.marking

theorem PELModuli.PELFamilyIso.complex_abelian_eq_id_ofBase {S : Scheme} (hS : S = Foundations.Scheme.ProjectiveSpace.complexBase)
    {P : PEL.PELFamilyData R g N S} (e : PELModuli.PELFamilyIso P P)
    (hP : P.IsPEL δ c) (hN : 3 ≤ N) : e.abelian.hom = 𝟙 P.abelian.scheme := by
  subst S
  exact PELModuli.PELFamilyIso.complex_abelian_eq_id e hP hN

theorem PELModuli.PELFamilyIso.complex_abelian_eq_id_via {Q : PEL.PELFamilyData R g N Foundations.Scheme.ProjectiveSpace.complexBase}
    (e : PELModuli.PELFamilyIso P P) (a : PELModuli.PELFamilyIso P Q)
    (hQ : Q.IsPEL δ c) (hN : 3 ≤ N) : e.abelian.hom = 𝟙 P.abelian.scheme := by
  have hj := PELModuli.PELFamilyIso.complex_abelian_eq_id (P := Q) (δ := δ) (c := c)
    (a.symm.trans (e.trans a)) hQ hN
  change a.abelian.inv ≫ (e.abelian.hom ≫ a.abelian.hom) = 𝟙 Q.abelian.scheme at hj
  have hh := congrArg (fun z => a.abelian.hom ≫ z ≫ a.abelian.inv) hj
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.id_comp, Category.comp_id] using hh

theorem PELModuli.PELFamilyIso.complex_abelian_eq_id_via_ofBase {S : Scheme} (hS : S = Foundations.Scheme.ProjectiveSpace.complexBase)
    {P Q : PEL.PELFamilyData R g N S} (e : PELModuli.PELFamilyIso P P) (a : PELModuli.PELFamilyIso P Q)
    (hQ : Q.IsPEL δ c) (hN : 3 ≤ N) : e.abelian.hom = 𝟙 P.abelian.scheme := by
  subst S
  exact PELModuli.PELFamilyIso.complex_abelian_eq_id_via e a hQ hN

end AlgebraicGeometry.AbelianScheme.TateComparison

end

end OAI

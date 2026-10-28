import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.AmbientClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates

/-! # Ambient Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.AmbientClass

noncomputable section

/-! Forgetting the support of the actual localized fixed point gives
one ambient class, independent of the principal parameter family. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (z : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion z]
  (hbase : z ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)

abbrev ambientMap := by
  letI : ∀ q, ((Survivor.dual f z B).X q).IsQuasicoherent :=
    fun q => PrincipalConcentration.terms_qc f z B hB q
  exact LocalClass.globalCoordinate f z hbase B hB ≫
    PrincipalReference.AmbientClass.Reference.ambient U hU (Survivor.dual f z B) (n+1)
      (Survivor.exactAt f z hbase B hB) (n+1)

variable {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (z ≫ f).ker.ideal ⟨U, hU⟩)

omit [Module.Injective R R] in
 theorem map_forget :
    LocalClass.map f z hbase B hB U hU s t hst ≫
      (Principal.AdditiveSections.forgetScalars U).map
        (homologyMap (AugmentedOrdered.CechForget.forgetSupport
          (PrincipalPoint.Fraction.family U t)
          (LocalCoordinates.principalDual f z B U hU)) (n+1)) =
    ambientMap f z hbase B hB U hU := by
  let : ∀ q, ((Survivor.dual f z B).X q).IsQuasicoherent :=
    fun q => PrincipalConcentration.terms_qc f z B hB q
  have h := PrincipalReference.AmbientClass.Reference.localize_forget U hU (Survivor.dual f z B) (n+1)
    (Survivor.exactAt f z hbase B hB) (PrincipalPoint.Fraction.family U t)
    (z ≫ f) (Survivor.forms (R := R)) (Survivor.adjunctionIso f z hbase B hB)
    (PrincipalConcentration.parameters_outside f z U hU s t hst) (n+1)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun a => LocalClass.globalCoordinate f z hbase B hB ≫ a) h)

variable [IsArtinianRing R] [IsLocalRing R]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

abbrev point := ambientMap f z hbase B hB U hU
  (SupportedClass.fixedPointClass f z hbase B hB)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
 theorem pointClass_forget :
    homologyMap (AugmentedOrdered.CechForget.forgetSupport
      (PrincipalPoint.Fraction.family U t)
      (LocalCoordinates.principalDual f z B U hU)) (n+1)
        (LocalClass.pointClass f z hbase B hB U hU s t hst) =
    point f z hbase B hB U hU :=
  ConcreteCategory.congr_hom (map_forget f z hbase B hB U hU s t hst)
    (SupportedClass.fixedPointClass f z hbase B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.AmbientClass

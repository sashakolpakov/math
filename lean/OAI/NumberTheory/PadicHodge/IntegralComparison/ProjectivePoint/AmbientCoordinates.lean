import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.AmbientClass

/-! # Ambient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.AmbientCoordinates

noncomputable section

/-! The ambient image of the actual point class is independent of
its local equations also at the full Koszul degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem transport_apply {F G : ℕ → Type u} (a : ∀ q, F q → G q)
    {i j : ℕ} (h : i = j) (x : F j) :
    a i (Eq.mpr (congrArg F h) x) = Eq.mpr (congrArg G h) (a j x) := by
  subst j
  rfl

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (z : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion z]
  (hbase : z ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  [IsArtinianRing R] [IsLocalRing R]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  {c m : ℕ} (hcm : c+m=n+1)

def ambientAt : (AugmentedOrdered.CechForget.ambientComplex (LocalCoordinates.principalDual f z B U hU)).homology (c+m) := by
  rw [hcm]
  exact AmbientClass.point f z hbase B hB U hU

variable (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (z ≫ f).ker.ideal ⟨U, hU⟩)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem pointAt_forget :
    homologyMap (AugmentedOrdered.CechForget.forgetSupport (PrincipalPoint.Fraction.family U t)
      (LocalCoordinates.principalDual f z B U hU)) (c+m)
        (LocalCoordinates.pointAt f z hbase B hB U hU s t hst hcm) =
      ambientAt f z hbase B hB U hU hcm := by
  have h := transport_apply
    (F := fun q => ((AugmentedOrdered.CechFunctor.bicomplex (PrincipalPoint.Fraction.family U t)
      (LocalCoordinates.principalDual f z B U hU)).total (.up ℕ)).homology q)
    (G := fun q => (AugmentedOrdered.CechForget.ambientComplex (LocalCoordinates.principalDual f z B U hU)).homology q)
    (fun q => homologyMap (AugmentedOrdered.CechForget.forgetSupport (PrincipalPoint.Fraction.family U t)
      (LocalCoordinates.principalDual f z B U hU)) q) hcm
    (LocalClass.pointClass f z hbase B hB U hU s t hst)
  rw [AmbientClass.pointClass_forget] at h
  exact h

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem independent
    (s' : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
    (t' : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
    (hst' : KoszulPartial.Resolution.pointIdeal
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s' t' = (z ≫ f).ker.ideal ⟨U, hU⟩) :
    homologyMap (AugmentedOrdered.CechForget.forgetSupport (PrincipalPoint.Fraction.family U t)
      (LocalCoordinates.principalDual f z B U hU)) (c+m) (LocalCoordinates.pointAt f z hbase B hB U hU s t hst hcm) =
    homologyMap (AugmentedOrdered.CechForget.forgetSupport (PrincipalPoint.Fraction.family U t')
      (LocalCoordinates.principalDual f z B U hU)) (c+m) (LocalCoordinates.pointAt f z hbase B hB U hU s' t' hst' hcm) :=
  (pointAt_forget f z hbase B hB U hU hcm s t hst).trans
    (pointAt_forget f z hbase B hB U hU hcm s' t' hst').symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.AmbientCoordinates

import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Topology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AffineAcyclicity

/-! # Basis Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisCohomology

noncomputable section

/-! # IntegralComparison: actual abelian cohomology on the affine principal-open basis -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R]

abbrev PrincipalSheaf := Sheaf (Topology.topology R) AddCommGrpCat.{u + 1}
abbrev AmbientSheaf := Lifted.AffineAcyclicity.AmbientSheaf R

instance principalHasSheafify : HasSheafify (Topology.topology R) AddCommGrpCat.{u + 1} :=
  AbelianSheafUniverses.hasSheafify.{u + 1, u, u} _

instance principalEnoughInjectives : EnoughInjectives (PrincipalSheaf R) :=
  AbelianSheafUniverses.enoughInjectives.{u + 1, u, u} _

instance principalHasExt : HasExt.{u + 2} (PrincipalSheaf R) := HasExt.standard _

instance structuredLimits (V : (Opens (PrimeSpectrum R))ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (PrincipalOpens.Category.toOpens R).op) AddCommGrpCat.{u + 1} :=
  HasLimitsOfShape.of_small.{u + 1, u + 1} _ _

instance basisDense : (PrincipalOpens.Category.toOpens R).IsDenseSubsite
    (Topology.topology R) (Opens.grothendieckTopology (PrimeSpectrum R)) := by
  unfold Topology.topology
  infer_instance

abbrev restriction : AmbientSheaf R ⥤ PrincipalSheaf R :=
  (Topology.sheafEquiv R AddCommGrpCat.{u + 1}).inverse

instance restriction_additive : (restriction R).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U x
    rfl

abbrev constantUnit : PrincipalSheaf R :=
  (constantSheaf (Topology.topology R) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

def constantTransport :
    (restriction R).obj (Lifted.AffineAcyclicity.constantUnit R) ≅ constantUnit R :=
  (Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    (Topology.topology R) (Opens.grothendieckTopology (PrimeSpectrum R))
    (PrincipalOpens.Category.toOpens R) AddCommGrpCat.{u + 1}).symm.app
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

def cohomologyEquiv (N : AmbientSheaf R) (n : ℕ) :
    Abelian.Ext.{u + 2} (Lifted.AffineAcyclicity.constantUnit R) N n ≃+
      Abelian.Ext.{u + 2} (constantUnit R) ((restriction R).obj N) n :=
  (AddEquiv.ofBijective ((restriction R).mapExtAddHom (Lifted.AffineAcyclicity.constantUnit R) N n)
    ((restriction R).mapExt_bijective_of_preservesInjectiveObjects _ _ n)).trans
      (AlgebraicGeometry.SheafCohomology.ExtLeft.Projective.extLeftIso (constantTransport R) ((restriction R).obj N) n)

def unitSheaf : PrincipalSheaf R :=
  (restriction R).obj (Lifted.AffineAcyclicity.unitSheaf R)

theorem positive_cohomology_zero (q : ℕ) :
    Subsingleton (Abelian.Ext.{u + 2} (constantUnit R) (unitSheaf R) (q + 1)) := by
  let := Lifted.AffineAcyclicity.positive_cohomology_zero R q
  exact (cohomologyEquiv R (Lifted.AffineAcyclicity.unitSheaf R) (q + 1)).symm.toEquiv.subsingleton

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisCohomology

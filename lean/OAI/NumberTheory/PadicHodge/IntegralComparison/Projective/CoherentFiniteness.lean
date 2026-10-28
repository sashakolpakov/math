import OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness

/-! # Coherent Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness

noncomputable section

/-!
# IntegralComparison: coherent cohomology finiteness from the actual projective embedding

The geometric projectivity predicate supplies a finite standard affine
cover. The proved projective Čech finiteness and affine Čech comparison
then give finite generation of actual coherent sheaf cohomology over
the Noetherian coefficient ring.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

theorem projectiveSpaceToSpec_eq (n : ℕ) : Projectivity.Construction.projectiveSpaceToSpec R n =
    AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) := rfl

theorem base_cohomology_finite [IsNoetherianRing R] [IsSeparated f]
    (hprojective : Projectivity.Construction.ProjectiveOver R f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M q
    Module.Finite Γ(Spec (CommRingCat.of R), ⊤) (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q) := by
  obtain ⟨n, i, hi, hπ⟩ := hprojective
  change X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) at i
  let : IsClosedImmersion i := hi
  let U := fun j : ULift (Fin (n + 1)) =>
    i ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) j
  have hU : IsOpenCover U :=
    (IsOpenCover.mk (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top
      (R := R) (σ := Fin (n + 1)))).comap i.base.hom
  have hUaff (j : ULift (Fin (n + 1))) : IsAffineOpen (U j) :=
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage i
  have hfinite :=
    AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite.MvPolynomial.closedImmersion_finiteType_orderedBaseCechComplex_homology_module_finite
      (R := R) i M q
  change i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) = f at hπ
  erw [hπ] at hfinite
  let : Module.Finite Γ(Spec (CommRingCat.of R), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U).homology q) := hfinite
  let : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from f]
    infer_instance
  exact AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness.baseCohomologyFinite_of_orderedBaseCech f M U hU hUaff q

@[instance_reducible]
def coefficientModule (M : X.Modules) (q : ℕ) : Module R (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q) := by
  letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M q
  exact Module.compHom _ (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

def baseToCoefficientSemilinear (M : X.Modules) (q : ℕ) :
    letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M q
    letI := coefficientModule R f M q
    AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q →ₛₗ[(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom] AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q := by
  letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M q
  letI := coefficientModule R f M q
  refine { toFun := id, map_add' := fun _ _ => rfl, map_smul' := ?_ }
  intro r x
  change r • x = (Scheme.ΓSpecIso (CommRingCat.of R)).inv
    ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r) • x
  have hr : (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r) = r :=
    ConcreteCategory.congr_hom (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of R))) r
  rw [hr]

theorem cohomology_finite [IsNoetherianRing R] [IsSeparated f]
    (hprojective : Projectivity.Construction.ProjectiveOver R f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    letI := coefficientModule R f M q
    Module.Finite R (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q) := by
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M q
  let := coefficientModule R f M q
  let : Module.Finite Γ(Spec (CommRingCat.of R), ⊤) (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q) :=
    base_cohomology_finite R f hprojective M q
  exact Module.Finite.of_surjective (baseToCoefficientSemilinear R f M q)
    Function.surjective_id

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness

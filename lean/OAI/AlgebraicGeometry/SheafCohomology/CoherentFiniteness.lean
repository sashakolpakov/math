import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexBase
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.LinearComparison

/-! # Coherent Finiteness -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CoherentFiniteness.Projective

noncomputable section

/-! Finiteness of the actual coherent cohomology of complex abelian varieties. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem zariskiBaseCohomology_finite (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    letI := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
    Module.Finite Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) (AffineH.Projective.H M q) := by
  obtain ⟨n, i, hi, hπ⟩ := Projective.ComplexBase.exists_standardProjectiveClosedImmersion A
  let : IsClosedImmersion i := hi
  let U := fun j : ULift (Fin (n + 1)) =>
    i ⁻¹ᵁ Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ) j
  have hU : IsOpenCover U :=
    (IsOpenCover.mk (Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top
      (R := ℂ) (σ := Fin (n + 1)))).comap i.base.hom
  have hUaff (j : ULift (Fin (n + 1))) : IsAffineOpen (U j) :=
    (Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := ℂ) j).preimage i
  have hfinite :=
    Projective.TwistCechFinite.MvPolynomial.closedImmersion_finiteType_orderedBaseCechComplex_homology_module_finite
      (R := ℂ) i M q
  rw [hπ] at hfinite
  let : Module.Finite Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)
      ((Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.variety.structureMap M U).homology q) :=
    hfinite
  let : IsNoetherianRing Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) := isNoetherianRing_of_ringEquiv ℂ
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
  let : A.carrier.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.variety.structureMap]
    infer_instance
  exact Projective.BaseFiniteness.baseCohomologyFinite_of_orderedBaseCech
    A.variety.structureMap M U hU hUaff q

def zariskiBaseToComplexSemilinear (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) (q : ℕ) :
    letI := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
    letI := Scalars.Projective.zariskiComplexCohomologyModule A M q
    AffineH.Projective.H M q →ₛₗ[(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom] AffineH.Projective.H M q := by
  letI := AffineH.Projective.globalSectionsCohomologyModule M q
  letI := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
  letI := Scalars.Projective.zariskiComplexCohomologyModule A M q
  refine { toFun := id, map_add' := fun _ _ => rfl, map_smul' := ?_ }
  intro r x
  change A.variety.structureMap.appTop r • x =
    A.variety.structureMap.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r)) • x
  have hr : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) = r :=
    ConcreteCategory.congr_hom (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of ℂ))) r
  rw [hr]

theorem zariskiComplexCohomology_finite (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    letI := Scalars.Projective.zariskiComplexCohomologyModule A M q
    Module.Finite ℂ (AffineH.Projective.H M q) := by
  let := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
  let := Scalars.Projective.zariskiComplexCohomologyModule A M q
  let : Module.Finite Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) (AffineH.Projective.H M q) :=
    zariskiBaseCohomology_finite A M q
  exact Module.Finite.of_surjective (zariskiBaseToComplexSemilinear A M q)
    Function.surjective_id

theorem coherentCohomology_finite (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite ℂ (Sheaves.Projective.coherentCohomology A M q) := by
  let := Scalars.Projective.zariskiComplexCohomologyModule A M q
  let : Module.Finite ℂ (AffineH.Projective.H M q) := zariskiComplexCohomology_finite A M q
  exact Module.Finite.equiv (LinearComparison.Projective.coherentCohomologyLinearEquivZariski A M q).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.CoherentFiniteness.Projective

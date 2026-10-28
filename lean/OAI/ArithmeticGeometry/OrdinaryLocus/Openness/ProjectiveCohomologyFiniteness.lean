import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseRingCohomologyScalars
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness

/-! # Projective Cohomology Finiteness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCohomologyFiniteness.Construction

noncomputable section

/-! Actual cohomology finiteness over a Noetherian affine base for projectively embedded schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def baseRingCohomologySemilinear (f : X ⟶ Spec (.of R)) (M : X.Modules) (n : ℕ) :
    letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
    letI := BaseRingCohomologyScalars.Construction.baseRingSheafCohomologyModule f M n
    AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n →ₛₗ[(Scheme.ΓSpecIso (.of R)).hom.hom] AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n := by
  letI := AlgebraicGeometry.SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule M n
  letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  letI := BaseRingCohomologyScalars.Construction.baseRingSheafCohomologyModule f M n
  refine { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := ?_ }
  intro r x
  change f.appTop r • x =
    f.appTop ((Scheme.ΓSpecIso (.of R)).inv ((Scheme.ΓSpecIso (.of R)).hom r)) • x
  have hr := ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of R)).hom_inv_id r
  change (Scheme.ΓSpecIso (.of R)).inv ((Scheme.ΓSpecIso (.of R)).hom r) = r at hr
  rw [hr]

theorem isFiniteType_of_isLineBundle (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M) : M.IsFiniteType := by
  have : M.IsFinitePresentation := LineBundleQuasicoherent.Construction.isFinitePresentation_of_isLineBundle M hM
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
  constructor
  intro i
  exact (hq.isFinite_presentation i).isFiniteType_generators

theorem projectiveEmbedding_sheafCohomology_finite [IsNoetherianRing R] [X.IsSeparated]
    {σ : Type} [Fintype σ] [LinearOrder σ]
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    letI := BaseRingCohomologyScalars.Construction.baseRingSheafCohomologyModule (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) M n
    Module.Finite R (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n) := by
  let f := i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := fun j : ULift σ ↦ i ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) j
  have hU : IsOpenCover U :=
    (IsOpenCover.mk (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))).comap i.base.hom
  have hUaff (j : ULift σ) : IsAffineOpen (U j) :=
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage i
  let : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let : Module.Finite Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U).homology n) :=
    AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite.MvPolynomial.closedImmersion_finiteType_orderedBaseCechComplex_homology_module_finite i M n
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  let : Module.Finite Γ(Spec (.of R), ⊤) (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n) :=
    AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness.baseCohomologyFinite_of_orderedBaseCech f M U hU hUaff n
  let := BaseRingCohomologyScalars.Construction.baseRingSheafCohomologyModule f M n
  exact Module.Finite.of_surjective (baseRingCohomologySemilinear f M n) Function.surjective_id

theorem projectiveEmbedding_lineBundleCohomology_finite [IsNoetherianRing R] [X.IsSeparated]
    {σ : Type} [Fintype σ] [LinearOrder σ]
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M) (n : ℕ) :
    letI := BaseRingCohomologyScalars.Construction.baseRingSheafCohomologyModule (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) M n
    Module.Finite R (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n) := by
  have := LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle M hM
  have := isFiniteType_of_isLineBundle M hM
  exact projectiveEmbedding_sheafCohomology_finite i M n

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCohomologyFiniteness.Construction

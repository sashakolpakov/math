import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechFlat
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatCech
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedHomology
import Mathlib.RingTheory.RingHom.Finite

/-! # Finite Cech Model -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.FiniteCechModel.Construction

noncomputable section

/-! Proper flat native Cech complexes have finite projective models
over the literal Noetherian base ring, with arbitrary tensor comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
theorem finite_restrictScalars_of_finite_hom {R S : Type} [CommRing R] [CommRing S]
    (ρ : R →+* S) (hρ : ρ.Finite) (M : ModuleCat S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars ρ).obj M) := by
  let : Algebra R S := ρ.toAlgebra
  let : Module R M := Module.compHom M ρ
  have : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  have : Module.Finite R S := hρ
  exact Module.Finite.trans S M

set_option backward.isDefEq.respectTransparency false in
theorem relativeStructureCech_homology_finite
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [IsProper f]
    {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Module.Finite R ((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).homology q) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) :=
    isNoetherianRing_of_surjective R _ (Scheme.ΓSpecIso (.of R)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).surjective
  let L := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFiniteType := by
    let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  let C := SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f L.sheaf U
  have : Module.Finite Γ(Spec (.of R), ⊤) (C.homology q) := by
    let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f L.sheaf q
    have := PELModuli.IntegralModel.Proper.CoherentCohomology.proper_coherent_cohomologyFinite_affine f L.sheaf q
    exact Module.Finite.equiv (SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv f L.sheaf U hU ha q).symm
  let ρ := (Scheme.ΓSpecIso (.of R)).inv.hom
  have : Module.Finite R ((ModuleCat.restrictScalars ρ).obj (C.homology q)) :=
    finite_restrictScalars_of_finite_hom ρ
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).surjective) _
  exact Module.Finite.equiv (Quotients.FiniteDescent.RestrictedHomology.Construction.RestrictedHomologyFinite.iso ρ C q).symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
theorem relativeStructureCech_exists_finite_projective_model
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
    {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) :
    ∃ (D : CochainComplex (ModuleCat.{0} R) ℕ) (φ : D ⟶ FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U),
      QuasiIso φ ∧ (∀ q, Module.Finite R (D.X q)) ∧ (∀ q, Module.Projective R (D.X q)) ∧
      (∀ (M : Type) [AddCommGroup M] [Module R M], QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map M φ)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨D, φ, hφ, _, hf, hp, ht⟩ :=
    Quotients.FiniteDescent.BoundedProjectiveComplex.Construction.CochainFiniteModel.exists_finite_projective_complex (FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U)
      ⟨Fintype.card ι, fun q hq =>
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map_isZero
          (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U q hq)⟩
      (CechFlat.Construction.relativeStructureCech_flat f U ha) (relativeStructureCech_homology_finite f U hU ha)
  exact ⟨D, φ, hφ, hf, hp, ht⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.FiniteCechModel.Construction

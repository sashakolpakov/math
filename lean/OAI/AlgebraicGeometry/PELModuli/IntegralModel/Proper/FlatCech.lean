import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CoherentCohomology
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechFlat
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BoundedProjectiveComplex
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange

/-! # Flat Cech -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatCech

noncomputable section

/-! A bounded finite projective complex computes a line bundle on a
proper flat scheme and its actual affine base changes. No projective
presentation of the scheme is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

theorem properFlat_exists_finite_projective_cech_model
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) :
    ∃ (D : CochainComplex (ModuleCat.{0} Γ(S, ⊤)) ℕ)
      (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f L.sheaf U),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite Γ(S, ⊤) (D.X q)) ∧
      (∀ q, Module.Projective Γ(S, ⊤) (D.X q)) ∧
      (∀ (A : Type) [AddCommGroup A] [Module Γ(S, ⊤) A],
        QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFiniteType := by
    let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  let : Fintype ι := Fintype.ofFinite ι
  apply Quotients.FiniteDescent.BoundedProjectiveComplex.Construction.CochainFiniteModel.exists_finite_projective_complex (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f L.sheaf U)
  · exact ⟨Fintype.card ι, SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le f L.sheaf U⟩
  · exact fun q => Quotients.FiniteDescent.OrderedCechObject.Construction.OrderedCechFlat.complex f L.sheaf (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)
      U (fun q i => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U ha q i) q
  · intro q
    let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f L.sheaf q
    have := CoherentCohomology.proper_coherent_cohomologyFinite_affine f L.sheaf q
    exact Module.Finite.equiv
      (SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv f L.sheaf U hU ha q).symm

theorem properFlat_exists_affine_baseChange_model
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) :
    ∃ (D : CochainComplex (ModuleCat.{0} Γ(S, ⊤)) ℕ)
      (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f L.sheaf U),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite Γ(S, ⊤) (D.X q)) ∧
      (∀ q, Module.Projective Γ(S, ⊤) (D.X q)) ∧
      (∀ (Y T : Scheme.{0}) [IsAffine T] (a : Y ⟶ X) (ρ : Y ⟶ T)
        (g : T ⟶ S) (hp : IsPullback a ρ f g),
        QuasiIso (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a f ρ g hp.w L.sheaf U φ)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨D, φ, hφ, hb, hf, hp, ht⟩ :=
    properFlat_exists_finite_projective_cech_model f L U hU ha
  refine ⟨D, φ, hφ, hb, hf, hp, ?_⟩
  intro Y T _ a ρ g h
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  exact Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso a f ρ g L.sheaf U φ h
    (fun q i => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U ha q i.1) ht

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatCech

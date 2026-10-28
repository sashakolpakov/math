import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel

/-! # Field Cohomology Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldCohomologyModel

noncomputable section

/-! Proper line-bundle cohomology over a field has a bounded finite projective model over the field itself. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem properField_exists_finite_coefficient_cech_model
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (L : Line.Bundles.LineBundle X) {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) :
    ∃ (D : CochainComplex (ModuleCat.{u} K) ℕ)
      (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf U),
      QuasiIso φ ∧ (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite K (D.X q)) ∧ (∀ q, Module.Projective K (D.X q)) ∧
      (∀ (A : Type u) [AddCommGroup A] [Module K A], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : L.sheaf.IsFiniteType := L.isFiniteType
  let : Fintype ι := Fintype.ofFinite ι
  apply Bounded.FiniteProjectiveComplex.CochainFiniteModel.exists_finite_projective_complex
    (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf U)
  · exact ⟨Fintype.card ι,
      Ordered.CoefficientCechComplex.orderedCoefficientCechObject_isZero_of_card_le (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf U⟩
  · intro q
    infer_instance
  · intro q
    have := CoherentCohomology.proper_coherent_cohomologyFinite p L.sheaf q
    exact Module.Finite.equiv
      (OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf U hU ha q).symm.toLinearEquiv

theorem properField_lineBundle_exists_finite_cohomology_model
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (L : Line.Bundles.LineBundle X) :
    ∃ D : CochainComplex (ModuleCat.{u} K) ℕ,
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite K (D.X q)) ∧ (∀ q, Module.Projective K (D.X q)) ∧
      (∀ q, Nonempty (D.homology q ≅
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj L.sheaf)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  obtain ⟨k, V, ha, _, hcover⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin k) → X.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hUa : ∀ i, IsAffineOpen (U i) := fun i => ha i.down
  obtain ⟨D, φ, hφ, hb, hf, hp, _⟩ :=
    properField_exists_finite_coefficient_cech_model p L U hU hUa
  have := hφ
  refine ⟨D, hb, hf, hp, fun q => ⟨?_⟩⟩
  exact isoOfQuasiIsoAt φ q ≪≫
    OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf U hU hUa q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldCohomologyModel

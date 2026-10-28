import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiberCohomologyModel

/-! # Fiberwise Cohomology Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberwiseCohomologyModel

noncomputable section

/-! A single bounded finite projective model computes a proper flat line bundle and every actual residue fiber, including their full coefficient actions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem properFlat_exists_fiberwise_cohomology_model
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) :
    ∃ D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ,
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite Γ(S, ⊤) (D.X q)) ∧ (∀ q, Module.Projective Γ(S, ⊤) (D.X q)) ∧
      (∀ q, Nonempty (D.homology q ≅
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom q).obj L.sheaf)) ∧
      (∀ (x : S) q, Nonempty
        ((((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj D).homology q ≅
            (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.fiberToSpecResidueField x).appTop.hom q).obj
              (L.pullback (f.fiberι x)).sheaf)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  obtain ⟨k, V, ha, he, hcover⟩ := L.exists_finite_affine_frames
  let U : ULift.{u} (Fin k) → X.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hUa : ∀ i, IsAffineOpen (U i) := fun i => ha i.down
  have hUe : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
      Line.Bundles.structureModule (U i).toScheme) := fun i => he i.down
  obtain ⟨D, φ, hφ, hb, hfin, hproj, ht⟩ := FiniteCechModel.properFlat_exists_finite_projective_cech_model f L U hU hUa
  have := hφ
  refine ⟨D, hb, hfin, hproj, fun q => ⟨?_⟩, ?_⟩
  · exact isoOfQuasiIsoAt φ q ≪≫ OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso f.appTop.hom L.sheaf U hU hUa q
  · intro x q
    let H := IsPullback.of_hasPullback f (S.fromSpecResidueField x)
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ) :=
      ht (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x))
    have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U hUa hUe
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
        Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := quasiIso_comp _ _
    exact ⟨Geometric.FiberCohomologyModel.fiberModelCohomologyIso f L U hU hUa φ x q⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberwiseCohomologyModel

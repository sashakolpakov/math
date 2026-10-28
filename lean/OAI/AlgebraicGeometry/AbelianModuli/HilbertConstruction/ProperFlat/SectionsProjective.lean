import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiberModelProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberModelIntrinsicExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionBaseChange

/-! # Sections Projective -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionsProjective

noncomputable section

/-! Vanishing of first cohomology on all fibers makes the actual global sections of a proper flat line bundle finite projective over a Noetherian affine base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem properFlat_sections_finite_projective_of_fiber_H1_vanishing
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    (hH : ∀ x : S, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1)) :
    Module.Finite Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (op ⊤)) ∧
      Module.Projective Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (op ⊤)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
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
  obtain ⟨D, φ, hφ, _, hfin, hproj, ht⟩ := FiniteCechModel.properFlat_exists_finite_projective_cech_model f L U hU hUa
  have := hφ
  have : Module.Finite Γ(S, ⊤) (D.X 0) := hfin 0
  have : Module.Projective Γ(S, ⊤) (D.X 0) := hproj 0
  have : Module.Finite Γ(S, ⊤) (D.X 1) := hfin 1
  have : Module.Projective Γ(S, ⊤) (D.X 1) := hproj 1
  have : Module.Finite Γ(S, ⊤) (D.X 2) := hfin 2
  have : Module.Projective Γ(S, ⊤) (D.X 2) := hproj 2
  have hD : ∀ x : S, (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj D).ExactAt 1 := by
    intro x
    let H := IsPullback.of_hasPullback f (S.fromSpecResidueField x)
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ) :=
      ht (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x))
    have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U hUa hUe
    have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
        Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := quasiIso_comp _ _
    exact FiberModelIntrinsicExactness.fiber_model_native_exact_of_H1_vanishing f L U hU hUa φ x (hH x)
  have : Module.Projective Γ(S, ⊤) (D.d 0 1).hom.ker := Affine.FiberModelProjectivity.affine_fiberModel_firstCycles_projective S D hD
  let e := Cech.ModelGlobalSections.CechModelSections.equiv f.appTop.hom L.sheaf U hU φ
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionsProjective

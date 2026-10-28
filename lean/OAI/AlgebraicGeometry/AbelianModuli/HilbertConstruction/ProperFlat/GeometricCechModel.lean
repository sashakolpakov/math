import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineCechTensorIsomorphism

/-! # Geometric Cech Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.GeometricCechModel

noncomputable section

/-! The constructed finite projective model computes every actual affine base change on a fixed finite affine frame cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem properFlat_exists_geometric_cech_model
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme)) :
    ∃ (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
      (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite Γ(S, ⊤) (D.X q)) ∧
      (∀ q, Module.Projective Γ(S, ⊤) (D.X q)) ∧
      (∀ (Y P : Scheme.{u}) [IsAffine Y] (a : P ⟶ X) (b : P ⟶ Y)
        (g : Y ⟶ S) (H : IsPullback a b f g),
        QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
          Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨D, φ, hφ, hb, hf, hp, ht⟩ := FiniteCechModel.properFlat_exists_finite_projective_cech_model f L U hU ha
  refine ⟨D, φ, hφ, hb, hf, hp, ?_⟩
  intro Y P _ a b g H
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U ha he
  exact quasiIso_comp _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.GeometricCechModel

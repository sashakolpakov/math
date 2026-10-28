import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.FirstCyclesBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberResidueModelExactness

/-! # Fiber Model Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiberModelProjectivity

noncomputable section

/-! A finite projective cochain model with zero first cohomology on all actual scheme fibers has a projective degree-zero cycle module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem affine_fiberModel_firstCycles_projective
    (S : Scheme.{u}) [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
    (hD : ∀ x : S, (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj D).ExactAt 1) :
    Module.Projective Γ(S, ⊤) (D.d 0 1).hom.ker := by
  have : Module.FinitePresentation Γ(S, ⊤) (D.d 0 1).hom.ker :=
    Module.finitePresentation_of_finite Γ(S, ⊤) _
  apply StalkProjectivity.affineModule_projective_of_stalkTensor_free S (D.d 0 1).hom.ker
  intro x
  let A := S.presheaf.stalk x
  let : Algebra Γ(S, ⊤) A := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : Module.Flat Γ(S, ⊤) A := FiberScalar.FiberScalarMaps.stalk_flat S x
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₁ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 0))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₁ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 0))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₂ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 1))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₂ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 1))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₃ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 2))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₃ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 2))
  exact (HilbertConstruction.Flat.FirstCyclesBaseChange.LocalSectionLifting.firstCycles_finite_free_after_flat_local_baseChange
    (D.sc' 0 1 2) (FiberResidueModelExactness.fiber_model_residue_exact S x D (hD x))).2

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiberModelProjectivity

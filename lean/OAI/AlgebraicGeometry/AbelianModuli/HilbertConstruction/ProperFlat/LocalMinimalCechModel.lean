import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MinimalShortComplex

/-! # Local Minimal Cech Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.LocalMinimalCechModel

noncomputable section

/-! Proper flat line bundles over Noetherian affine local bases have actual universal finite free Cech models and local minimal short complexes. Both models are constructed; neither is supplied as a hypothesis. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem properFlat_exists_local_minimal_cech_model
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) :
    ∃ (C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
      (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U)
      (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (C.X q)) ∧
      (∀ q, Module.Finite Γ(S, ⊤) (C.X q)) ∧
      (∀ q, Module.Free Γ(S, ⊤) (C.X q)) ∧
      (∀ (B : Type u) [AddCommGroup B] [Module Γ(S, ⊤) B],
        QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ)) ∧
      Q.complex.f.hom.baseChange (IsLocalRing.ResidueField Γ(S, ⊤)) = 0 ∧
      Q.complex.g.hom.baseChange (IsLocalRing.ResidueField Γ(S, ⊤)) = 0 := by
  obtain ⟨C, φ, hφ, hb, hf, hp, ht⟩ :=
    FiniteCechModel.properFlat_exists_finite_projective_cech_model f L U hU ha
  have hfree (q : ℕ) : Module.Free Γ(S, ⊤) (C.X q) := by
    have : Module.Finite Γ(S, ⊤) (C.X q) := hf q
    have : Module.Projective Γ(S, ⊤) (C.X q) := hp q
    exact Module.free_of_flat_of_isLocalRing
  let T := C.sc' 0 1 2
  have : Module.Finite Γ(S, ⊤) T.X₁ := hf 0
  have : Module.Free Γ(S, ⊤) T.X₁ := hfree 0
  have : Module.Finite Γ(S, ⊤) T.X₂ := hf 1
  have : Module.Free Γ(S, ⊤) T.X₂ := hfree 1
  have : Module.Finite Γ(S, ⊤) T.X₃ := hf 2
  have : Module.Free Γ(S, ⊤) T.X₃ := hfree 2
  obtain ⟨Q⟩ := Local.MinimalShortComplex.LocalSectionLifting.exists_localMinimalShortComplex T
  exact ⟨C, φ, Q, hφ, hb, hf, hfree, ht, Q.incoming_residue_zero, Q.outgoing_residue_zero⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.LocalMinimalCechModel

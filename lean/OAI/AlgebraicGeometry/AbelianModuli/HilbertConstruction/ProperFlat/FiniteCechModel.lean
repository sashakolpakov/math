import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineCoherentCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.LineBundleCechFlat
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FiniteProjectiveComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections

/-! # Finite Cech Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel

noncomputable section

/-! A bounded finite projective complex computes a line bundle on a proper flat scheme over a Noetherian affine base, and its comparison remains a quasi-isomorphism after tensoring with every coefficient module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem properFlat_exists_finite_projective_cech_model
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) :
    ∃ (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
      (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite Γ(S, ⊤) (D.X q)) ∧
      (∀ q, Module.Projective Γ(S, ⊤) (D.X q)) ∧
      (∀ (A : Type u) [AddCommGroup A] [Module Γ(S, ⊤) A],
        QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : L.sheaf.IsFiniteType := L.isFiniteType
  let : Fintype ι := Fintype.ofFinite ι
  apply Bounded.FiniteProjectiveComplex.CochainFiniteModel.exists_finite_projective_complex
    (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U)
  · exact ⟨Fintype.card ι, Ordered.CoefficientCechComplex.orderedCoefficientCechObject_isZero_of_card_le f.appTop.hom L.sheaf U⟩
  · exact fun q => Ordered.LineBundleCechFlat.orderedLineBundleCechComplex_flat f L U (Affine.CechIntersections.affine_cechIntersection U ha) q
  · intro q
    have := Proper.AffineCoherentCohomology.proper_coherent_cohomologyFinite_affine f L.sheaf q
    exact Module.Finite.equiv (OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso f.appTop.hom L.sheaf U hU ha q).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelTensorKoszulComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.ResidueCohomology

/-! # Model Residue Dimensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelResidueDimensions

noncomputable section

/-! Every residue-field specialization of the constructed minimal local model has binomial cohomology dimensions in all degrees. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem minimalModel_closedField_cohomology_finrank
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (rs : List R) (hlen : rs.length = g) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R) (hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R))
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))
    (e : R ≃ₗ[R] Q.complex.X₁) (hI : Q.firstDifferentialIdeal = maximalIdeal R)
    (B : Type u) [Field B] [Algebra R B]
    (hkill : maximalIdeal R ≤ RingHom.ker (algebraMap R B)) (q : ℕ) :
    Module.finrank B
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology q) =
      g.choose q := by
  have hrs : ∀ r ∈ rs, algebraMap R B r = 0 := by
    intro r hr
    apply hkill
    rw [← hgen]
    exact Ideal.subset_span hr
  let E := ModelTensorKoszulComparison.minimalModelMappedKoszulDualHomologyIso (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B)
    C g hfin hfree hbound rs hlen hreg hgen hfield Q e hI q
  exact E.toLinearEquiv.finrank_eq.trans
    (by simpa only [hlen] using ScalarKoszul.ResidueCohomology.scalarKoszulChainDual_baseChange_homology_finrank B rs hrs q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelResidueDimensions

import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomZero
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinAdjunction

/-! # Compact Top Open Generation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactTopOpenGeneration.Constructions

noncomputable section

/-! Native compact Poincare duality transports open generation of H₀ to top compact cohomology. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M] [ChartedSpace (Fin d → ℂ) M]
variable [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem compactTop_hom_ext_openCover {ι : Type*}
    (U : ι → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i) {A : ModuleCat.{0} ℚ}
    {f g : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2*d) ⟶ A}
    (h : ∀ i, AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) (U i) (2*d) ≫ f =
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) (U i) (2*d) ≫ g) : f = g := by
  let eM := AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := M) (2*d) 0 rfl
  apply (cancel_epi eM.inv).mp
  apply CompactThomZero.Constructions.rationalHomologyZero_hom_ext_openCover (TopCat.of M) U hcover
  intro i
  let eU := AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := U i) (2*d) 0 rfl
  apply (cancel_epi eU.hom).mp
  have hc := AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality.complexManifoldCompactSupportCap_open d (U i) (2*d) 0 rfl
  change AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) (U i) (2*d) ≫ eM.hom =
    eU.hom ≫ AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
      (Opens.inclusion' (X := TopCat.of M) (U i)) 0 at hc
  simp only [← Category.assoc]
  rw [← hc]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h i

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactTopOpenGeneration.Constructions

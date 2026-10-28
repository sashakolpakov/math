import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalFactorCechTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalCechFactorVanishing

/-! # External First Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalFirstCohomology

noncomputable section

/-! If the proper-factor line bundle has no cohomology below degree q, and the parameter-factor line bundle has no global sections, then their actual external tensor product has vanishing cohomology in degree q. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
variable [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
variable (heV : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable {κ : Type u} [Finite κ] (U : κ → Y.Opens)
variable (hU : iSup U = ⊤) (haU : ∀ i, IsAffineOpen (U i))
variable (heU : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

include H hV haV heV hU haU heU in
theorem fieldExternalTensor_firstCohomology_vanish (n : ℕ)
    (hL : ∀ r, r < n + 1 → Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf r))
    (hN : Subsingleton Γ(N.sheaf, ⊤)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (((L.pullback a).tensor (N.pullback b)).sheaf) (n + 1)) := by
  let E := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)
  change Subsingleton (CategoryTheory.Sheaf.H E (n + 1))
  apply Cech.FirstCohomology.IntrinsicCech.cech_firstCohomology_vanish_of_factors E (fun i => b ⁻¹ᵁ U i)
    (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top b U hU) n
  · intro p r hr i
    exact ExternalCechFactorVanishing.fieldExternal_cechTermFactor_cohomology_vanish H L N V hV haV heV U haU heU
      p i r (hL r hr)
  · exact ExternalFactorCechTensor.fieldExternal_cechCohomology_firstDifferential_injective H L N V hV haV heV U haU heU
      hU hN n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalFirstCohomology

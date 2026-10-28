import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorAllCohomology
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # External Cech Factor Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalCechFactorVanishing

noncomputable section

/-! Over a field, lower-degree vanishing transfers to every actual tuple factor of the product Cech resolution, including degree zero. Both covers and all frames are actual geometric data. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
variable [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
variable (heV : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable {κ : Type u} (U : κ → Y.Opens) (haU : ∀ i, IsAffineOpen (U i))
variable (heU : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

include H hV haV heV haU heU in
theorem fieldExternal_cechTermFactor_cohomology_vanish
    (p : ℕ) (i : Fin (p + 1) → κ) (r : ℕ)
    (hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf r)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (IntrinsicCech.SheafTerms.cechTermFactor (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))
        (fun i => b ⁻¹ᵁ U i) p i) r) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let W : Y.Opens := ∏ᶜ fun j : Fin (p + 1) => U (i j)
  have hW : IsAffineOpen W := Affine.CechIntersections.affine_cechIntersection U haU p i
  have hle : W ≤ U (i 0) := leOfHom (Pi.π (fun j : Fin (p + 1) => U (i j)) 0)
  let eW := N.frameRestrict hle (heU (i 0)).some
  change Subsingleton (CategoryTheory.Sheaf.H
    ((IntrinsicCech.SheafComplex.cechFactorPresheaf (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))).obj
      (op (∏ᶜ fun j : Fin (p + 1) => b ⁻¹ᵁ U (i j)))) r)
  rw [← CoefficientCech.PushforwardFactors.preimageCechIntersection b U p i]
  exact Intrinsic.ExternalFactorAllCohomology.nativeExternalFactor_cohomology_vanish H L N W hW eW V hV haV heV r hL

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalCechFactorVanishing

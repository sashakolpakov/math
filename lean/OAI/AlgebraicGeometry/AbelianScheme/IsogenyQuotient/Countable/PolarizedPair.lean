import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.DualProjectivity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Models

/-! # Polarized Pair -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PolarizedPair.Construction

noncomputable section

/-! The original abelian variety and its original dual descend together
to full abelian schemes over one countable algebraically closed subfield. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

def polarizedAbelianPair : Bool → AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))
  | false => A.abelian
  | true => A.dual.abelian

theorem countable_polarized_pair_model_exists :
    Nonempty (Models.Construction.CountableAbelianFamilyModel (fun _ : Bool => g) (polarizedAbelianPair A)) := by
  let n : Bool → ℕ
    | false => (AbelianModuli.ReferenceFamily.Geometric.PolarizedProjectivity.geometricPolarizedProjectivePresentation A).dimension
    | true => (Geometric.DualProjectivity.Construction.geometricDualProjectivePresentation A).dimension
  have hm (b : Bool) : Nonempty (AbelianModuli.ReferenceFamily.Geometric.GroupModel.GeometricGroupModel (polarizedAbelianPair A b).scheme (n b)) := by
    cases b
    · exact AbelianModuli.ReferenceFamily.Geometric.AbelianModel.geometricPolarized_has_abelian_model A
    · exact Geometric.DualProjectivity.Construction.geometricDual_has_group_model A
  exact Models.Construction.countable_abelian_family_model_exists (fun _ : Bool => g) (polarizedAbelianPair A)
    n (fun b => (hm b).some)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PolarizedPair.Construction

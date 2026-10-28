import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

/-! # Tensor Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor products of line bundles commute with every scheme base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem LineBundle.TensorBaseChange.tensorPullbackComparison_comp_isIso_iff (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules)
    [IsIso (Tensor.PullbackComparison.tensorPullbackComparison f ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullback g).obj N))] :
    IsIso ((Scheme.Modules.pullback f).map (Tensor.PullbackComparison.tensorPullbackComparison g M N)) ↔
      IsIso (Tensor.PullbackComparison.tensorPullbackComparison (f ≫ g) M N) := by
  have h := congrArg IsIso (Tensor.PullbackComposition.tensorPullbackComparison_comp f g M N)
  simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using h.to_iff

/-- Local triviality makes the canonical tensor comparison invertible for arbitrary morphisms. -/
theorem LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso (f : X ⟶ Y) (L M : Line.Bundles.LineBundle Y) :
    IsIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial (f x)
  obtain ⟨V, hxV, ⟨d⟩⟩ := M.locallyTrivial (f x)
  let W := U ⊓ V
  let eW := L.frameRestrict (show W ≤ U from inf_le_left) e
  let dW := M.frameRestrict (show W ≤ V from inf_le_right) d
  have hW : IsIso (Tensor.PullbackComparison.tensorPullbackComparison (f ∣_ W)
      ((Scheme.Modules.pullback W.ι).obj L.sheaf)
      ((Scheme.Modules.pullback W.ι).obj M.sheaf)) :=
    Tensor.PullbackComposition.tensorPullbackComparison_isIso_of_trivial (f ∣_ W) eW dW
  have hc : IsIso (Tensor.PullbackComparison.tensorPullbackComparison ((f ∣_ W) ≫ W.ι) L.sheaf M.sheaf) :=
    (LineBundle.TensorBaseChange.tensorPullbackComparison_comp_isIso_iff (f ∣_ W) W.ι L.sheaf M.sheaf).mp
      ((Scheme.Modules.pullback (f ∣_ W)).map_isIso _)
  have hc' : IsIso (Tensor.PullbackComparison.tensorPullbackComparison ((f ⁻¹ᵁ W).ι ≫ f) L.sheaf M.sheaf) := by
    rw [← morphismRestrict_ι f W]
    exact hc
  refine ⟨f ⁻¹ᵁ W, ⟨hxU, hxV⟩, ?_⟩
  exact (LineBundle.TensorBaseChange.tensorPullbackComparison_comp_isIso_iff (f ⁻¹ᵁ W).ι f L.sheaf M.sheaf).mpr hc'

/-- The actual tensor line bundle and arbitrary pullback commute. -/
def Line.Bundles.LineBundle.tensorBaseChangeIso (f : X ⟶ Y) (L M : Line.Bundles.LineBundle Y) :
      ((L.tensor M).pullback f).sheaf ≅ ((L.pullback f).tensor (M.pullback f)).sheaf := by
  exact @asIso X.Modules _ _ _ (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf)
    (LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f L M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

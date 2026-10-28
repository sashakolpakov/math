import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackComposition
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackOpen
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackUnit

/-! # Tensor Pullback -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap

noncomputable section

/-! Tensor powers of actual line bundles commute with arbitrary scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem isIso_comp_iff (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (n : ℕ)
    [IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f ((Scheme.Modules.pullback g).obj L) n)] :
    IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison (f ≫ g) L n) ↔
      IsIso ((Scheme.Modules.pullback f).map (TensorPullbackSpec.Construction.TensorPullbackMap.comparison g L n)) := by
  have : IsIso (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).inv.app L) n) :=
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).map_isIso _
  have h := congrArg (fun a => IsIso a) (TensorPullbackComposition.Construction.TensorPullbackMap.comparison_comp f g L n)
  simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using h.to_iff

/-- The comparison is invertible for every line bundle, without any
flatness or open-immersion assumption on the scheme morphism. -/
theorem isIso (f : X ⟶ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (n : ℕ) :
    IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f L.sheaf n) := by
  apply AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial (f x)
  let W : X.Opens := f ⁻¹ᵁ U
  refine ⟨W, hx, ?_⟩
  have : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison U.ι L.sheaf n) := TensorPullbackOpen.Construction.TensorPullbackMap.isIso_of_isOpenImmersion U.ι L.sheaf n
  have : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison (f ∣_ U) ((Scheme.Modules.pullback U.ι).obj L.sheaf) n) :=
    TensorPullbackUnit.Construction.TensorPullbackMap.isIso_of_frame (f ∣_ U) e n
  have hc : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison ((f ∣_ U) ≫ U.ι) L.sheaf n) :=
    (isIso_comp_iff (f ∣_ U) U.ι L.sheaf n).mpr inferInstance
  have hc' : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison (W.ι ≫ f) L.sheaf n) :=
    (congrArg (fun k : W.toScheme ⟶ Y => IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison k L.sheaf n))
      (morphismRestrict_ι f U)).mp hc
  have : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison W.ι ((Scheme.Modules.pullback f).obj L.sheaf) n) :=
    TensorPullbackOpen.Construction.TensorPullbackMap.isIso_of_isOpenImmersion W.ι _ n
  exact (isIso_comp_iff W.ι f L.sheaf n).mp hc'

/-- The constructed pullback–tensor-power isomorphism for arbitrary base change. -/
def iso (f : X ⟶ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (n : ℕ) :
    ((L.tensorPower n).pullback f).sheaf ≅ ((L.pullback f).tensorPower n).sheaf :=
  @asIso X.Modules _ _ _ (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f L.sheaf n) (isIso f L n)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.PullbackUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

/-! # Power Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every tensor power of a line bundle commutes with arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem LineBundle.PowerBaseChange.powerPullbackComparison_comp_isIso_iff (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules)
    (n : ℕ) [IsIso (Power.PullbackComparison.powerPullbackComparison f ((Scheme.Modules.pullback g).obj L) n)] :
    IsIso ((Scheme.Modules.pullback f).map (Power.PullbackComparison.powerPullbackComparison g L n)) ↔
      IsIso (Power.PullbackComparison.powerPullbackComparison (f ≫ g) L n) := by
  have : IsIso (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).hom.app L) n) :=
    (TensorPower.Maps.tensorPowerFunctor X n).map_isIso _
  have h := congrArg IsIso (Power.PullbackComposition.powerPullbackComparison_comp f g L n)
  simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using h.to_iff

theorem LineBundle.PowerBaseChange.powerPullbackComparison_isIso_of_trivial {L : Y.Modules} (f : X ⟶ Y)
    (e : L ≅ Line.Bundles.structureModule Y) (n : ℕ) : IsIso (Power.PullbackComparison.powerPullbackComparison f L n) := by
  have : IsIso (TensorPower.Maps.tensorPowerMap e.hom n) := (TensorPower.Maps.tensorPowerFunctor Y n).map_isIso _
  have : IsIso (TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullback f).map e.hom) n) :=
    (TensorPower.Maps.tensorPowerFunctor X n).map_isIso _
  have h : IsIso (Power.PullbackComparison.powerPullbackComparison f L n ≫
      TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullback f).map e.hom) n) := by
    rw [← Power.PullbackComparison.powerPullbackComparison_natural]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

theorem LineBundle.PowerBaseChange.lineBundle_powerPullbackComparison_isIso (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y) (n : ℕ) :
    IsIso (Power.PullbackComparison.powerPullbackComparison f L.sheaf n) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial (f x)
  have hU : IsIso (Power.PullbackComparison.powerPullbackComparison (f ∣_ U) ((Scheme.Modules.pullback U.ι).obj L.sheaf) n) :=
    LineBundle.PowerBaseChange.powerPullbackComparison_isIso_of_trivial (f ∣_ U) e n
  have hc : IsIso (Power.PullbackComparison.powerPullbackComparison ((f ∣_ U) ≫ U.ι) L.sheaf n) :=
    (LineBundle.PowerBaseChange.powerPullbackComparison_comp_isIso_iff (f ∣_ U) U.ι L.sheaf n).mp
      ((Scheme.Modules.pullback (f ∣_ U)).map_isIso _)
  have hc' : IsIso (Power.PullbackComparison.powerPullbackComparison ((f ⁻¹ᵁ U).ι ≫ f) L.sheaf n) := by
    rw [← morphismRestrict_ι f U]
    exact hc
  exact ⟨f ⁻¹ᵁ U, hxU, (LineBundle.PowerBaseChange.powerPullbackComparison_comp_isIso_iff (f ⁻¹ᵁ U).ι f L.sheaf n).mpr hc'⟩

def Line.Bundles.LineBundle.powerBaseChangeIso (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y) (n : ℕ) :
    ((L.tensorPower n).pullback f).sheaf ≅ ((L.pullback f).tensorPower n).sheaf := by
  exact @asIso X.Modules _ _ _ (Power.PullbackComparison.powerPullbackComparison f L.sheaf n)
    (LineBundle.PowerBaseChange.lineBundle_powerPullbackComparison_isIso f L n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

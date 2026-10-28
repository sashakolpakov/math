import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps

/-! # Multiplication Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Multiplication by sections and all degree transitions commute with open
restriction under the canonical comparison of tensor-power sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M N : Y.Modules} {n : ℕ}

theorem Tensor.Powers.SheafMultilinearMap.insertSection_postcomp (β : Tensor.Powers.SheafMultilinearMap L (n + 1) M)
    (s : Line.Bundles.structureModule Y ⟶ L) (a : M ⟶ N) :
    (β.postcomp a).insertSection s = (β.insertSection s).postcomp a := by
  ext U v
  rfl

theorem Tensor.Powers.SheafMultilinearMap.restrict_insertSection (f : X ⟶ Y) [IsOpenImmersion f]
    (β : Tensor.Powers.SheafMultilinearMap L (n + 1) M) (s : Line.Bundles.structureModule Y ⟶ L) :
    (β.insertSection s).restrict f = (β.restrict f).insertSection (Section.SectionRestriction.restrictSection f s) := by
  ext U v
  change β.app (f ''ᵁ U) (Fin.cons (s.app (f ''ᵁ U) (1 : Γ(Y, f ''ᵁ U))) v) =
    β.app (f ''ᵁ U) (Fin.cons ((Section.SectionRestriction.restrictSection f s).app U (1 : Γ(X, U))) v)
  exact congrArg (fun z : Γ(L, f ''ᵁ U) => β.app (f ''ᵁ U) (Fin.cons z v))
    (Section.SectionRestriction.restrictSection_app_one f s U).symm

/-- Multiplication by a section commutes with the canonical restriction comparison. -/
theorem Power.MultiplicationRestriction.tensorPowerRestrictIso_multiply (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) :
    (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n).hom ≫ (Scheme.Modules.restrictFunctor f).map (Section.PowerMultiplication.multiplyPowerBySection s n) =
      Section.PowerMultiplication.multiplyPowerBySection (Section.SectionRestriction.restrictSection f s) n ≫ (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L (n + 1)).hom := by
  have h₀ : (TensorPower.Maps.tensorPowerMultilinear (L.restrict f) n).postcomp (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n).hom =
      (TensorPower.Maps.tensorPowerMultilinear L n).restrict f := TensorPower.RestrictionMaps.tensorPowerRestrictHom_spec f L n
  have h₁ : (TensorPower.Maps.tensorPowerMultilinear (L.restrict f) (n + 1)).postcomp
      (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L (n + 1)).hom =
        (TensorPower.Maps.tensorPowerMultilinear L (n + 1)).restrict f := TensorPower.RestrictionMaps.tensorPowerRestrictHom_spec f L (n + 1)
  apply TensorPower.Maps.tensorPower_hom_ext
  rw [Tensor.Powers.SheafMultilinearMap.postcomp_comp, h₀, ← Tensor.Powers.SheafMultilinearMap.restrict_postcomp,
    Section.PowerMultiplication.multiplyPowerBySection_spec, Tensor.Powers.SheafMultilinearMap.restrict_insertSection, ← h₁,
    Tensor.Powers.SheafMultilinearMap.insertSection_postcomp, ← Section.PowerMultiplication.multiplyPowerBySection_spec,
    ← Tensor.Powers.SheafMultilinearMap.postcomp_comp]

/-- Every iterated section transition commutes with open restriction. -/
theorem Power.MultiplicationRestriction.tensorPowerRestrictIso_transition (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (n m : ℕ) :
    (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n).hom ≫ (Scheme.Modules.restrictFunctor f).map (Power.SectionTransitions.powerSectionTransition s n m) =
      Power.SectionTransitions.powerSectionTransition (Section.SectionRestriction.restrictSection f s) n m ≫ (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L (n + m)).hom := by
  induction m with
  | zero =>
    change (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n).hom ≫ (Scheme.Modules.restrictFunctor f).map (𝟙 _) =
      𝟙 _ ≫ (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n).hom
    rw [(Scheme.Modules.restrictFunctor f).map_id, Category.comp_id, Category.id_comp]
  | succ m ih =>
    change (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n).hom ≫ (Scheme.Modules.restrictFunctor f).map
      (Power.SectionTransitions.powerSectionTransition s n m ≫ Section.PowerMultiplication.multiplyPowerBySection s (n + m)) =
        (Power.SectionTransitions.powerSectionTransition (Section.SectionRestriction.restrictSection f s) n m ≫
          Section.PowerMultiplication.multiplyPowerBySection (Section.SectionRestriction.restrictSection f s) (n + m)) ≫
            (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L (n + m + 1)).hom
    rw [(Scheme.Modules.restrictFunctor f).map_comp, ← Category.assoc, ih, Category.assoc,
      Power.MultiplicationRestriction.tensorPowerRestrictIso_multiply, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafZeroExact.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleCompatibility

/-! # Zero Cycle Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleLifting.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

theorem cechZeroCycle_component_eq {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (s : (IntrinsicCech.SheafTerms.cechTerm F U 0).obj.obj (op V))
    (hs : (SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s = 0)
    (i : Fin 1 → ι) :
    F.obj.map (homOfLE (inf_le_left :
        (V ⊓ (∏ᶜ fun k : Fin 1 => U (i k))) ≤ V)).op
        (F.obj.map (eqToHom (congrArg op (ZeroCycleIndices.IntrinsicCech.cechConstIntersection_eq U i₀ hV)))
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s (ZeroCycleIndices.IntrinsicCech.cechConstIndex i₀))) =
      IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s i := by
  let j := ZeroCycleIndices.IntrinsicCech.cechPairIndex i₀ i
  have hToPair :
      V ⊓ (∏ᶜ fun k : Fin 1 => U (i k)) ≤
        ∏ᶜ fun k : Fin 2 => U (j k) := by
    exact leOfHom (Pi.lift fun k : Fin 2 => homOfLE (by
      fin_cases k
      · exact inf_le_left.trans hV
      · exact inf_le_right.trans
          (leOfHom (Pi.π (fun k : Fin 1 => U (i k)) 0))))
  have hBack :
      V ⊓ (∏ᶜ fun k : Fin 1 => U (i k)) ≤
        V ⊓ (∏ᶜ fun k : Fin 2 => U (j k)) :=
    le_inf inf_le_left hToPair
  calc
    _ = F.obj.map (homOfLE hBack).op
          (F.obj.map (homOfLE (inf_le_inf_left V (ZeroCycleIndices.IntrinsicCech.cechPairLEOne U i₀ i))).op
            (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s (ZeroCycleIndices.IntrinsicCech.cechConstIndex i₀))) := by
      change (F.obj.map _ ≫ F.obj.map _) _ =
        (F.obj.map _ ≫ F.obj.map _) _
      exact ConcreteCategory.congr_hom
        ((F.obj.map_comp _ _).symm.trans
          ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
            (F.obj.map_comp _ _))) _
    _ = F.obj.map (homOfLE hBack).op
        (F.obj.map (homOfLE (inf_le_inf_left V (ZeroCycleIndices.IntrinsicCech.cechPairLEZero U i₀ i))).op
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s i)) :=
      congrArg (fun y => F.obj.map (homOfLE hBack).op y)
        (ZeroCycleCompatibility.IntrinsicCech.cechZeroCycle_pair_restrictions_eq F U i₀ s hs i).symm
    _ = _ := by
      change (F.obj.map _ ≫ F.obj.map _) _ = _
      exact ConcreteCategory.congr_hom
        ((F.obj.map_comp _ _).symm.trans
          ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
            (F.obj.map_id _))) _

/-- A degree-zero Cech cycle on an open contained in one cover member is the
augmentation of a section on that open. -/
theorem exists_preimage_cechAugmentation_of_le {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (s : (IntrinsicCech.SheafTerms.cechTerm F U 0).obj.obj (op V))
    (hs : (SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s = 0) :
    ∃ t : F.obj.obj (op V),
      (SheafAugmentation.IntrinsicCech.cechAugmentation F U).hom.app (op V) t = s := by
  let t := F.obj.map (eqToHom (congrArg op (ZeroCycleIndices.IntrinsicCech.cechConstIntersection_eq U i₀ hV)))
    (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s (ZeroCycleIndices.IntrinsicCech.cechConstIndex i₀))
  refine ⟨t, (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V).injective ?_⟩
  funext i
  rw [SheafAugmentation.IntrinsicCech.cechAugmentation_apply]
  exact cechZeroCycle_component_eq F U i₀ hV s hs i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleLifting.IntrinsicCech

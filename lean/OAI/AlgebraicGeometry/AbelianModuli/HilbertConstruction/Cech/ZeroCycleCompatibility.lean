/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafZeroExact.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleIndices

/-! # Zero Cycle Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleCompatibility.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

theorem cechZeroCycle_pair_restrictions_eq {V : Opens X} (i₀ : ι)
    (s : (IntrinsicCech.SheafTerms.cechTerm F U 0).obj.obj (op V))
    (hs : (SheafDifferential.IntrinsicCech.cechDifferential F U 0).hom.app (op V) s = 0)
    (i : Fin 1 → ι) :
    F.obj.map (homOfLE (inf_le_inf_left V (ZeroCycleIndices.IntrinsicCech.cechPairLEZero U i₀ i))).op
        (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s i) =
      F.obj.map (homOfLE (inf_le_inf_left V (ZeroCycleIndices.IntrinsicCech.cechPairLEOne U i₀ i))).op
        (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s (ZeroCycleIndices.IntrinsicCech.cechConstIndex i₀)) := by
  let iZero := ZeroCycleIndices.IntrinsicCech.cechPairIndex i₀ i ∘
    (SimplexCategory.δ (0 : Fin 2)).toOrderHom
  let iOne := ZeroCycleIndices.IntrinsicCech.cechPairIndex i₀ i ∘
    (SimplexCategory.δ (1 : Fin 2)).toOrderHom
  have hd := congrArg (fun y => IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 1 V y
    (ZeroCycleIndices.IntrinsicCech.cechPairIndex i₀ i)) hs
  rw [SheafDifferential.IntrinsicCech.cechDifferential_apply] at hd
  simp only [Nat.reduceAdd, Int.reduceNeg, OrderHom.toFun_eq_coe,
    homOfLE_leOfHom, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, pow_zero, one_smul, Nat.mod_succ, pow_one, neg_smul,
    map_zero, Pi.zero_apply] at hd
  have htermZero :
      F.obj.map (homOfLE (inf_le_inf_left V
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ
              (ZeroCycleIndices.IntrinsicCech.cechPairIndex i₀ i))))).op
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s iZero) =
        F.obj.map (homOfLE (inf_le_inf_left V (ZeroCycleIndices.IntrinsicCech.cechPairLEZero U i₀ i))).op
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s i) := by
    rw [← LocalContractionSections.IntrinsicCech.cechTermSectionsAddEquiv_transport U F 0 V s (ZeroCycleIndices.IntrinsicCech.cechPairDeleteZero i₀ i)]
    change F.obj.map _ _ = (F.obj.map _ ≫ F.obj.map _) _
    exact ConcreteCategory.congr_hom
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        (F.obj.map_comp _ _)) _
  have htermOne :
      F.obj.map (homOfLE (inf_le_inf_left V
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ
              (ZeroCycleIndices.IntrinsicCech.cechPairIndex i₀ i))))).op
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s iOne) =
        F.obj.map (homOfLE (inf_le_inf_left V (ZeroCycleIndices.IntrinsicCech.cechPairLEOne U i₀ i))).op
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s (ZeroCycleIndices.IntrinsicCech.cechConstIndex i₀)) := by
    rw [← LocalContractionSections.IntrinsicCech.cechTermSectionsAddEquiv_transport U F 0 V s (ZeroCycleIndices.IntrinsicCech.cechPairDeleteOne i₀ i)]
    change F.obj.map _ _ = (F.obj.map _ ≫ F.obj.map _) _
    exact ConcreteCategory.congr_hom
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        (F.obj.map_comp _ _)) _
  let a := F.obj.map
    (homOfLE (inf_le_inf_left V (ZeroCycleIndices.IntrinsicCech.cechPairLEZero U i₀ i))).op
      (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s i)
  let b := F.obj.map
    (homOfLE (inf_le_inf_left V (ZeroCycleIndices.IntrinsicCech.cechPairLEOne U i₀ i))).op
      (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U 0 V s (ZeroCycleIndices.IntrinsicCech.cechConstIndex i₀))
  rw [htermZero, htermOne] at hd
  change a + -b = 0 at hd
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg] using hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleCompatibility.IntrinsicCech

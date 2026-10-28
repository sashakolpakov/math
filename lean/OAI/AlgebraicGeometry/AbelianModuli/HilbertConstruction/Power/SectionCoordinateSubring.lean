import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumSectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FactorizationSpans
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.MapSectionFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MultiplicationProduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisPullbackSectionSurjectivity

/-! # Section Coordinate Subring -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionCoordinateSubring

noncomputable section

/-! Consecutive section factorizations force every power numerator's chart
coordinate into the subring containing the degree-one coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

local instance powerSectionFrame {M : X.Modules} (U : X.Opens)
    (s : Line.Bundles.structureModule X ⟶ M) [IsIso (Ample.LineBundles.pullbackSection U.ι s)] (n : ℕ) :
    IsIso (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s n)) :=
  Nonvanishing.tensorPowerSection_pullback_isIso U.ι s n

private def frameCoordinateAddHom {Y : Scheme.{u}} {M : Y.Modules}
    (e : Line.Bundles.structureModule Y ⟶ M) [IsIso e] : (Line.Bundles.structureModule Y ⟶ M) →+ Γ(Y, ⊤) where
  toFun t := Frame.Coordinates.frameCoordinate e t
  map_zero' := by
    change Frame.Coordinates.structureModuleEndValue Y (0 ≫ inv e) = 0
    rw [zero_comp, map_zero]
  map_add' t v := by
    change Frame.Coordinates.structureModuleEndValue Y ((t + v) ≫ inv e) = _
    rw [Preadditive.add_comp, map_add]
    rfl

def sectionPowerCoordinateAddHom (L : Line.Bundles.LineBundle X) (U : X.Opens)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [IsIso (Ample.LineBundles.pullbackSection U.ι s)] (n : ℕ) :
    (Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf) →+ Γ(U.toScheme, ⊤) :=
  (frameCoordinateAddHom (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s n))).comp
    (BasisPullbackSectionSurjectivity.pullbackSectionAddHom U.ι (L.tensorPower n).sheaf)

theorem sectionPowerCoordinates_mem_of_factorization
    (L : Line.Bundles.LineBundle X) (U : X.Opens) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    [IsIso (Ample.LineBundles.pullbackSection U.ι s)] (C : Subring Γ(U.toScheme, ⊤))
    (hbase : ∀ t : Line.Bundles.structureModule X ⟶ (L.tensorPower 1).sheaf,
      sectionPowerCoordinateAddHom L U s 1 t ∈ C)
    (hfactor : ∀ m : ℕ, 0 < m → Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule X)
      (L.tensorPower m).sheaf (L.tensorPower (1 + m)).sheaf)
    (n : ℕ) (hn : 0 < n) (t : Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf) :
    sectionPowerCoordinateAddHom L U s n t ∈ C := by
  classical
  have h : ∀ m : ℕ, ∀ v : Line.Bundles.structureModule X ⟶ (L.tensorPower (m + 1)).sheaf,
      sectionPowerCoordinateAddHom L U s (m + 1) v ∈ C := by
    intro m
    induction m with
    | zero => exact hbase
    | succ m ih =>
      have hstep : ∀ v : Line.Bundles.structureModule X ⟶ (L.tensorPower (1 + (m + 1))).sheaf,
          sectionPowerCoordinateAddHom L U s (1 + (m + 1)) v ∈ C := by
        intro v
        obtain ⟨k, w, a, hv⟩ := hfactor (m + 1) (Nat.zero_lt_succ m) v
        choose z hz using fun i => LineBundle.MapSectionFactorization.tensorPowerMap_exists_multiplying_section L 1 (m + 1) (a i)
        rw [hv, map_sum]
        apply C.sum_mem
        intro i _
        have he : w i ≫ a i = Tensor.ProductSections.tensorProductSection (z i) (w i) ≫
            (L.tensorPowerAddIso 1 (m + 1)).inv := by
          rw [← hz i, ← Category.assoc, Section.MultiplicationProduct.section_comp_moduleSectionMultiply]
        rw [he]
        change Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s (1 + (m + 1))))
          (Ample.LineBundles.pullbackSection U.ι (Tensor.ProductSections.tensorProductSection (z i) (w i) ≫
            (L.tensorPowerAddIso 1 (m + 1)).inv)) ∈ C
        rw [SumSectionCoordinates.tensorPowerAddIso_product_coordinate]
        exact C.mul_mem (hbase (z i)) (ih (w i))
      rw [show m + 1 + 1 = 1 + (m + 1) by omega]
      exact hstep
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact h m t

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionCoordinateSubring

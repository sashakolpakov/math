import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCycleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdge
import Mathlib.Algebra.Group.Int.Units

/-! # Column Top Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnTopEdge

noncomputable section

/-! The original top-row edge is inverse to single-column concentration
with exactly the total-flip sign in bidegree (c,c). -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
variable {R : Type u} [CommRing R]
  (B : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.flip.X p).X q))
  (outgoing : ∀ q, (B.d c (c+1)).f q = 0)
local notation "T" => B.total (ComplexShape.up ℕ)
local notation "σ" => ComplexShape.σ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) c c
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCycleCoordinates.homologyIso B c hB c

/-- Exact cycle coordinate of the row inclusion, retaining the flip sign. -/
theorem cycle_coordinates :
    ModuleCat.ofHom (X := ModuleCat.of R (Module.CochainClasses.cycles (B.X c) c))
        (Y := ModuleCat.of R (Module.CochainClasses.cycles T (c+c))) (TopRowEdge.cycleMap B c outgoing c) ≫
      (Module.CochainClassNaturality.cyclesIso T (c+c)).hom ≫
        ColumnCycleCoordinates.cycleProjection B c hB c =
    σ • (Module.CochainClassNaturality.cyclesIso (B.X c) c).hom := by
  apply (cancel_mono ((B.X c).iCycles c)).mp
  have hi :
      ModuleCat.ofHom (X := ModuleCat.of R (Module.CochainClasses.cycles (B.X c) c))
          (Y := ModuleCat.of R (Module.CochainClasses.cycles T (c+c))) (TopRowEdge.cycleMap B c outgoing c) ≫
        (Module.CochainClassNaturality.cyclesIso T (c+c)).hom ≫ (T).iCycles (c+c) =
      (Module.CochainClassNaturality.cyclesIso (B.X c) c).hom ≫ (B.X c).iCycles c ≫
        B.ιTotal (.up ℕ) c c (c+c) rfl := by
    rw [Module.CochainClassNaturality.cyclesIso_hom_i, ← Category.assoc, Module.CochainClassNaturality.cyclesIso_hom_i]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  rw [Category.assoc, Category.assoc,
    ColumnCycleCoordinates.cycleProjection_i]
  rw [← Category.assoc _ _ (σ • AbelianSingleRowTotal.projection B c c (c+c) _),
    ← Category.assoc _ _ (σ • AbelianSingleRowTotal.projection B c c (c+c) _), hi]
  simp only [Units.smul_def, Category.assoc, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  simp [AbelianSingleRowTotal.projection]

/-- Concentration of a top-row class is its original class with the flip sign. -/
theorem class_coordinates (z : Module.CochainClasses.cycles (B.X c) c) :
    (e).hom (Module.CochainClasses.classMap T (c+c) (TopRowEdge.cycleMap B c outgoing c z)) =
      σ • Module.CochainClasses.classMap (B.X c) c z := by
  have he :
      ModuleCat.ofHom (X := ModuleCat.of R (Module.CochainClasses.cycles T (c+c)))
        (Y := (T).homology (c+c)) (Module.CochainClasses.classMap T (c+c)) ≫ (e).hom =
      (Module.CochainClassNaturality.cyclesIso T (c+c)).hom ≫
        ColumnCycleCoordinates.cycleProjection B c hB c ≫
          (B.X c).homologyπ c := by
    rw [Module.CochainClassNaturality.classMap_eq, Category.assoc,
      ColumnCycleCoordinates.homologyπ_coordinate]
  have h := congrArg (fun a =>
    ModuleCat.ofHom (X := ModuleCat.of R (Module.CochainClasses.cycles (B.X c) c))
      (Y := ModuleCat.of R (Module.CochainClasses.cycles T (c+c))) (TopRowEdge.cycleMap B c outgoing c) ≫ a) he
  have hc := congrArg (fun a => a ≫ (B.X c).homologyπ c)
    (cycle_coordinates B c hB outgoing)
  rw [Category.assoc] at hc
  have h' := h.trans hc
  have hz := ConcreteCategory.congr_hom h' z
  simpa only [Units.smul_def, Category.assoc, Preadditive.zsmul_comp,
    ← Module.CochainClassNaturality.classMap_eq, ConcreteCategory.comp_apply, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.smul_apply] using hz

theorem map_apply (x : (B.X c).homology c) :
    (e).hom (TopRowEdge.map B c outgoing c x) = σ • x := by
  obtain ⟨z, rfl⟩ := Module.CochainClasses.classMap_surjective (B.X c) c x
  rw [TopRowEdge.map_class]
  exact class_coordinates B c hB outgoing z

private theorem sign_self : σ * σ = 1 := by
  apply Units.ext
  exact Int.isUnit_mul_self (σ).isUnit

theorem inv_apply (x : (B.X c).homology c) :
    (e).inv x = σ • TopRowEdge.map B c outgoing c x := by
  apply (ModuleCat.mono_iff_injective (e).hom).mp inferInstance
  rw [Iso.inv_hom_id_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [map_apply]
  change x = σ • (σ • x)
  rw [smul_smul, sign_self, one_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnTopEdge

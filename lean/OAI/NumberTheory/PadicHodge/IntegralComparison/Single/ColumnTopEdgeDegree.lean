import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnTopEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdgeNaturality

/-! # Column Top Edge Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnTopEdgeDegree

noncomputable section

/-! The single-column edge formula in every bidegree. The original
edge is transported only along the equality of its total degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

namespace Row
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses
universe u v
variable {R : Type u} [CommRing R]
  (B : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  (c : ℕ) (hB : ∀ q, (B.d c (c+1)).f q = 0)

def mapTo (n N : ℕ) (h : c+n=N) :
    (B.X c).homology n →ₗ[R] (B.total (.up ℕ)).homology N :=
  h ▸ TopRowEdge.map B c hB n

theorem mapTo_class (n N : ℕ) (h : c+n=N) (x : Module.CochainClasses.cycles (B.X c) n) :
    mapTo B c hB n N h (Module.CochainClasses.classMap (B.X c) n x) =
      Module.CochainClasses.classMap (B.total (.up ℕ)) N (TopRowEdge.cycleMapTo B c hB n N h x) := by
  cases h
  exact TopRowEdge.map_class B c hB n x

variable (L : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  (hL : ∀ q, (L.d c (c+1)).f q = 0) (a : B ⟶ L)

theorem naturality (n N : ℕ) (h : c+n=N) (x : (B.X c).homology n) :
    homologyMap (HomologicalComplex₂.total.map a (.up ℕ)) N (mapTo B c hB n N h x) =
      mapTo L c hL n N h (homologyMap (a.f c) n x) := by
  cases h
  exact TopRowEdgeNaturality.naturality B L c hB hL a n x

end Row

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
variable {R : Type u} [CommRing R]
  (B : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.flip.X p).X q))
  (outgoing : ∀ q, (B.d c (c+1)).f q = 0) (n : ℕ)
local notation "T" => B.total (ComplexShape.up ℕ)
local notation "σ" => ComplexShape.σ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) c n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCycleCoordinates.homologyIso B c hB n

/-- Exact cycle coordinate of the row inclusion, retaining the flip sign. -/
theorem cycle_coordinates :
    ModuleCat.ofHom (X := ModuleCat.of R (Module.CochainClasses.cycles (B.X c) n))
        (Y := ModuleCat.of R (Module.CochainClasses.cycles T (n+c))) (TopRowEdge.cycleMapTo B c outgoing n (n+c) (Nat.add_comm c n)) ≫
      (Module.CochainClassNaturality.cyclesIso T (n+c)).hom ≫
        ColumnCycleCoordinates.cycleProjection B c hB n =
    σ • (Module.CochainClassNaturality.cyclesIso (B.X c) n).hom := by
  apply (cancel_mono ((B.X c).iCycles n)).mp
  have hi :
      ModuleCat.ofHom (X := ModuleCat.of R (Module.CochainClasses.cycles (B.X c) n))
          (Y := ModuleCat.of R (Module.CochainClasses.cycles T (n+c))) (TopRowEdge.cycleMapTo B c outgoing n (n+c) (Nat.add_comm c n)) ≫
        (Module.CochainClassNaturality.cyclesIso T (n+c)).hom ≫ (T).iCycles (n+c) =
      (Module.CochainClassNaturality.cyclesIso (B.X c) n).hom ≫ (B.X c).iCycles n ≫
        B.ιTotal (.up ℕ) c n (n+c) (Nat.add_comm c n) := by
    rw [Module.CochainClassNaturality.cyclesIso_hom_i, ← Category.assoc, Module.CochainClassNaturality.cyclesIso_hom_i]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  rw [Category.assoc, Category.assoc,
    ColumnCycleCoordinates.cycleProjection_i]
  rw [← Category.assoc _ _ (σ • AbelianSingleRowTotal.projection B c n (n+c) _),
    ← Category.assoc _ _ (σ • AbelianSingleRowTotal.projection B c n (n+c) _), hi]
  simp only [Units.smul_def, Category.assoc, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  simp [AbelianSingleRowTotal.projection]

/-- Concentration of a top-row class is its original class with the flip sign. -/
theorem class_coordinates (z : Module.CochainClasses.cycles (B.X c) n) :
    (e).hom (Module.CochainClasses.classMap T (n+c) (TopRowEdge.cycleMapTo B c outgoing n (n+c) (Nat.add_comm c n) z)) =
      σ • Module.CochainClasses.classMap (B.X c) n z := by
  have he :
      ModuleCat.ofHom (X := ModuleCat.of R (Module.CochainClasses.cycles T (n+c)))
        (Y := (T).homology (n+c)) (Module.CochainClasses.classMap T (n+c)) ≫ (e).hom =
      (Module.CochainClassNaturality.cyclesIso T (n+c)).hom ≫
        ColumnCycleCoordinates.cycleProjection B c hB n ≫
          (B.X c).homologyπ n := by
    rw [Module.CochainClassNaturality.classMap_eq, Category.assoc,
      ColumnCycleCoordinates.homologyπ_coordinate]
  have h := congrArg (fun a =>
    ModuleCat.ofHom (X := ModuleCat.of R (Module.CochainClasses.cycles (B.X c) n))
      (Y := ModuleCat.of R (Module.CochainClasses.cycles T (n+c))) (TopRowEdge.cycleMapTo B c outgoing n (n+c) (Nat.add_comm c n)) ≫ a) he
  have hc := congrArg (fun a => a ≫ (B.X c).homologyπ n)
    (cycle_coordinates B c hB outgoing n)
  rw [Category.assoc] at hc
  have h' := h.trans hc
  have hz := ConcreteCategory.congr_hom h' z
  simpa only [Units.smul_def, Category.assoc, Preadditive.zsmul_comp,
    ← Module.CochainClassNaturality.classMap_eq, ConcreteCategory.comp_apply, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.smul_apply] using hz

theorem map_apply (x : (B.X c).homology n) :
    (e).hom (Row.mapTo B c outgoing n (n+c) (Nat.add_comm c n) x) = σ • x := by
  obtain ⟨z, rfl⟩ := Module.CochainClasses.classMap_surjective (B.X c) n x
  rw [Row.mapTo_class]
  exact class_coordinates B c hB outgoing n z

private theorem sign_self : σ * σ = 1 := by
  apply Units.ext
  exact Int.isUnit_mul_self (σ).isUnit

theorem inv_apply (x : (B.X c).homology n) :
    (e).inv x = σ • Row.mapTo B c outgoing n (n+c) (Nat.add_comm c n) x := by
  apply (ModuleCat.mono_iff_injective (e).hom).mp inferInstance
  rw [Iso.inv_hom_id_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [map_apply]
  change x = σ • (σ • x)
  rw [smul_smul, sign_self, one_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnTopEdgeDegree

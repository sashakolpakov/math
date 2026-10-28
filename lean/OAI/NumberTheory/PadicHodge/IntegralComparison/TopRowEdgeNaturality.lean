import OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdge

/-! # Top Row Edge Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdgeNaturality

noncomputable section

/-! The final-row edge map commutes with the actual maps of double
complexes, including geometric pullback and coefficient reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
  (K L : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  [K.HasTotal (.up ℕ)] [L.HasTotal (.up ℕ)] (c : ℕ)
  (hK : ∀ q, (K.d c (c + 1)).f q = 0)
  (hL : ∀ q, (L.d c (c + 1)).f q = 0)
  (φ : K ⟶ L)

theorem cycle_naturality (n : ℕ) (x : Module.CochainClasses.cycles (K.X c) n) :
    TopRowEdge.cycleMap L c hL n (Module.CochainClassNaturality.cycleMap (φ.f c) n x) =
      Module.CochainClassNaturality.cycleMap (HomologicalComplex₂.total.map φ (.up ℕ))
        (c + n) (TopRowEdge.cycleMap K c hK n x) := by
  apply Subtype.ext
  change L.ιTotal (.up ℕ) c n (c + n) rfl ((φ.f c).f n x.val) =
    (HomologicalComplex₂.total.map φ (.up ℕ)).f (c + n)
      (K.ιTotal (.up ℕ) c n (c + n) rfl x.val)
  exact (ConcreteCategory.congr_hom (HomologicalComplex₂.ιTotal_map K L φ (.up ℕ) c n (c + n) rfl) x.val).symm

theorem naturality (n : ℕ) (x : (K.X c).homology n) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map φ (.up ℕ)) (c + n)
        (TopRowEdge.map K c hK n x) =
      TopRowEdge.map L c hL n (HomologicalComplex.homologyMap (φ.f c) n x) := by
  obtain ⟨z, rfl⟩ := Module.CochainClasses.classMap_surjective (K.X c) n x
  rw [TopRowEdge.map_class]
  rw [← Module.CochainClassNaturality.naturality_apply
    (HomologicalComplex₂.total.map φ (.up ℕ)) (c + n) (TopRowEdge.cycleMap K c hK n z)]
  rw [← cycle_naturality K L c hK hL φ n z]
  rw [← TopRowEdge.map_class L c hL n (Module.CochainClassNaturality.cycleMap (φ.f c) n z)]
  rw [Module.CochainClassNaturality.naturality_apply (φ.f c) n z]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdgeNaturality

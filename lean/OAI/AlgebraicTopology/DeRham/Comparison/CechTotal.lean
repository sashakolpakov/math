import OAI.AlgebraicTopology.DeRham.Comparison.CechColumns
import OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap

/-! # Cech Total -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CechTotal

noncomputable section

/-!
# Comparison of actual Čech total complexes

A coefficient map which is a quasi-isomorphism on every ordered cover
intersection induces a quasi-isomorphism of the actual Čech total complexes.
The proof first identifies columns with products of the intersection section
complexes, then applies the proved finite first-quadrant comparison theorem.
The resulting cohomology isomorphism is induced by the given coefficient map.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)
variable {K L K' L' : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ}

/-- Quasi-isomorphisms on all actual ordered intersections induce a
quasi-isomorphism of the signed Čech total complexes. -/
theorem cechTotalMap_quasiIso_of_intersections (φ : K ⟶ L)
    (hφ : ∀ (p : ℕ) (a : Fin (p + 1) → ι), QuasiIso (CechColumns.cechIntersectionMap U φ a)) :
    QuasiIso (CechTotalFunctor.cechTotalMap U φ) := by
  exact DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns (CechDoubleComplexFunctor.cechDoubleComplexMap U φ)
    (fun p => CechColumns.cechDoubleComplexMap_column_quasiIso U φ p (hφ p))

/-- The actual coefficient map induces this isomorphism on total cohomology. -/
def cechTotalCohomologyIso (φ : K ⟶ L)
    (hφ : ∀ (p : ℕ) (a : Fin (p + 1) → ι), QuasiIso (CechColumns.cechIntersectionMap U φ a))
    (n : ℕ) : (CechTotalFunctor.cechTotalComplex U K).homology n ≅ (CechTotalFunctor.cechTotalComplex U L).homology n := by
  let : QuasiIso (CechTotalFunctor.cechTotalMap U φ) := cechTotalMap_quasiIso_of_intersections U φ hφ
  exact isoOfQuasiIsoAt (CechTotalFunctor.cechTotalMap U φ) n

@[simp]
theorem cechTotalCohomologyIso_hom (φ : K ⟶ L)
    (hφ : ∀ (p : ℕ) (a : Fin (p + 1) → ι), QuasiIso (CechColumns.cechIntersectionMap U φ a))
    (n : ℕ) :
    (cechTotalCohomologyIso U φ hφ n).hom =
      HomologicalComplex.homologyMap (CechTotalFunctor.cechTotalMap U φ) n := rfl

/-- On cycle classes the isomorphism applies the actual total coefficient map. -/
theorem cechTotalCohomologyIso_class (φ : K ⟶ L)
    (hφ : ∀ (p : ℕ) (a : Fin (p + 1) → ι), QuasiIso (CechColumns.cechIntersectionMap U φ a))
    (n : ℕ) :
    (CechTotalFunctor.cechTotalComplex U K).homologyπ n ≫ (cechTotalCohomologyIso U φ hφ n).hom =
      HomologicalComplex.cyclesMap (CechTotalFunctor.cechTotalMap U φ) n ≫
        (CechTotalFunctor.cechTotalComplex U L).homologyπ n :=
  HomologicalComplex.homologyπ_naturality (CechTotalFunctor.cechTotalMap U φ) n

/-- Commutative squares of coefficient maps give commutative squares of the
actual total-cohomology comparison isomorphisms. -/
theorem cechTotalCohomologyIso_naturality
    (φ : K ⟶ L) (ψ : K' ⟶ L') (α : K ⟶ K') (β : L ⟶ L')
    (hcomm : α ≫ ψ = φ ≫ β)
    (hφ : ∀ (p : ℕ) (a : Fin (p + 1) → ι), QuasiIso (CechColumns.cechIntersectionMap U φ a))
    (hψ : ∀ (p : ℕ) (a : Fin (p + 1) → ι), QuasiIso (CechColumns.cechIntersectionMap U ψ a))
    (n : ℕ) :
    HomologicalComplex.homologyMap (CechTotalFunctor.cechTotalMap U α) n ≫
        (cechTotalCohomologyIso U ψ hψ n).hom =
      (cechTotalCohomologyIso U φ hφ n).hom ≫
        HomologicalComplex.homologyMap (CechTotalFunctor.cechTotalMap U β) n := by
  simp only [cechTotalCohomologyIso_hom, ← HomologicalComplex.homologyMap_comp,
    ← CechTotalFunctor.cechTotalMap_comp]
  rw [hcomm]

end

end OAI.AlgebraicTopology.DeRham.Comparison.CechTotal

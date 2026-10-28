import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ClosedFactorizationLocus

/-! # Factorization Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FactorizationIdeal

noncomputable section

/-! The closed factorization locus has an ideal whose pullback vanishes exactly when the family map factors, on arbitrary scheme tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X P Z : Over S}
variable [IsProper X.hom] [Flat X.hom] (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P)

theorem exists_proper_factorization_ideal :
    ∃ I : S.IdealSheafData, ∀ (T : Scheme.{u}) (c : T ⟶ S),
      I.comap c = ⊥ ↔
        ∃! h : (Over.pullback c).obj X ⟶ (Over.pullback c).obj Z,
          h ≫ (Over.pullback c).map j = (Over.pullback c).map i := by
  obtain ⟨B, k, hk, htest⟩ := ClosedFactorizationLocus.proper_closed_factorization_locus j i
  let : IsClosedImmersion k.left := hk
  refine ⟨k.left.ker, fun T c => ?_⟩
  have hc : (Over.mkIdTerminal.from (Over.mk c)).left = c := by
    simp
  have h := (Closed.ImmersionFactorization.closedImmersion_ideal_factorization k (Over.mkIdTerminal.from (Over.mk c))).trans
    (htest (Over.mk c)).symm
  rwa [hc] at h

def properFactorizationIdeal : S.IdealSheafData := (exists_proper_factorization_ideal j i).choose

theorem properFactorizationIdeal_test {T : Scheme.{u}} (c : T ⟶ S) :
    (properFactorizationIdeal j i).comap c = ⊥ ↔
      ∃! h : (Over.pullback c).obj X ⟶ (Over.pullback c).obj Z,
        h ≫ (Over.pullback c).map j = (Over.pullback c).map i :=
  (exists_proper_factorization_ideal j i).choose_spec T c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FactorizationIdeal

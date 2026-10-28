import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafStalkQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalEdge
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero

/-! # Sheaf Total Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafTotalEdge.ModuleSheafTotalEdge

noncomputable section

/-! Exact augmented rows compute the original complex of module sheaves through their first-quadrant total complex. -/

open _root_.CategoryTheory Limits

variable (R : Type) [CommRing R] (X : TopCat.{0})
  (B : HomologicalComplex₂ (TopCat.Sheaf (ModuleCat R) X) (.up ℕ) (.up ℕ))
  (K : CochainComplex (TopCat.Sheaf (ModuleCat R) X) ℕ)
  (e : ∀ q, K.X q ⟶ (B.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (B.d q q').f 0 = K.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (B.X q).d 0 1 = 0)

theorem quasiIso
    (haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : ∀ q p, (B.X q).ExactAt (p + 1)) :
    QuasiIso ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w) := by
  constructor
  intro n
  cases n with
  | zero => exact AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero B K e he w (haug 0) hmono
  | succ n =>
    apply (SheafStalkQuasiIso.ModuleSheafStalkQuasiIso.sheafQuasiIsoAt_iff_stalk R _ (n + 1)).mpr
    intro x
    let G := TopCat.Sheaf.forget (ModuleCat R) X ⋙ TopCat.Presheaf.stalkFunctor (ModuleCat R) x
    let F := G ⋙ forget₂ (ModuleCat R) AddCommGrpCat
    have h := TotalEdge.TotalEdgeComparison.mapped_edge_quasiIsoAt_succ F B K e he w haug hmono hrows n
    exact (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
      ((G.mapHomologicalComplex (.up ℕ)).map ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w))
      (forget₂ (ModuleCat R) AddCommGrpCat) (n + 1)).mp h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafTotalEdge.ModuleSheafTotalEdge

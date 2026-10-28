import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.SheafStalkQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalEdge
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero

/-! # Sheaf Total Edge -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.SheafTotalEdge.ModuleSheafTotalEdge

noncomputable section

/-! Exact augmented rows compute the original complex of module sheaves through their first-quadrant total complex. -/

open _root_.CategoryTheory Limits

universe u

variable (R : Type u) [CommRing R] (X : TopCat.{u})
  (B : HomologicalComplex₂ (TopCat.Sheaf (ModuleCat.{u} R) X) (.up ℕ) (.up ℕ))
  (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} R) X) ℕ)
  (e : ∀ q, K.X q ⟶ (B.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (B.d q q').f 0 = K.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (B.X q).d 0 1 = 0)

theorem quasiIso
    (haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : ∀ q p, (B.X q).ExactAt (p + 1)) :
    QuasiIso ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w) := by
  constructor
  intro n
  cases n with
  | zero => exact Comparison.Betti.TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero B K e he w (haug 0) hmono
  | succ n =>
    apply (SheafStalkQuasiIso.ModuleSheafStalkQuasiIso.sheafQuasiIsoAt_iff_stalk R _ (n + 1)).mpr
    intro x
    let G := TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙ TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x
    let F := G ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
    have h := NumberTheory.PadicHodge.GeometricComparison.TotalEdge.TotalEdgeComparison.mapped_edge_quasiIsoAt_succ F B K e he w haug hmono hrows n
    exact (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
      ((G.mapHomologicalComplex (.up ℕ)).map ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he w))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat) (n + 1)).mp h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.SheafTotalEdge.ModuleSheafTotalEdge

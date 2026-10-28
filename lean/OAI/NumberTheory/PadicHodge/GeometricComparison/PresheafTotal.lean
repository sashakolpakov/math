import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalEdge
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Presheaf Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafTotal.PresheafTotalEdge

noncomputable section

/-! Exact augmented rows give a quasi-isomorphism to the actual total
complex of module-valued presheaves, in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable (R : Type u) [CommRing R] {D : Type v} [Category.{w} D]
  (B : HomologicalComplex₂ (D ⥤ ModuleCat.{u} R) (.up ℕ) (.up ℕ))
  (K : CochainComplex (D ⥤ ModuleCat.{u} R) ℕ)
  (e : ∀ q, K.X q ⟶ (B.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (B.d q q').f 0 = K.d q q' ≫ e q')
  (hzero : ∀ q, e q ≫ (B.X q).d 0 1 = 0)

local instance hasTotal : B.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts B

theorem quasiIso
    (haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (hzero q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : ∀ q p, (B.X q).ExactAt (p + 1)) :
    QuasiIso ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he hzero) := by
  constructor
  intro n
  cases n with
  | zero => exact AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero B K e he hzero (haug 0) hmono
  | succ n =>
    apply (HomologicalComplex.quasiIsoAt_iff_evaluation _ (n + 1)).mpr
    intro T
    let G := (evaluation D (ModuleCat.{u} R)).obj T
    let F := G ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
    let : PreservesColimitsOfSize.{u, u} F := by
      dsimp only [F, G]
      infer_instance
    let : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
    have h := TotalEdge.TotalEdgeComparison.mapped_edge_quasiIsoAt_succ F B K e he hzero haug hmono hrows n
    exact (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
      ((G.mapHomologicalComplex (.up ℕ)).map ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he hzero))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (n + 1)).mp h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafTotal.PresheafTotalEdge

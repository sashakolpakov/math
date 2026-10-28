import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicCoverTotalVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison

/-! # Base Cover Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseCoverVanishing

noncomputable section

/-! Vanishing on the inverse images of all affine opens of a separated base implies actual global cohomology vanishing. The inverse images themselves need not be affine. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

theorem cohomology_vanish_of_affine_base_opens
    {X T : Scheme.{u}} [T.IsSeparated] (f : X ⟶ T) (M : X.Modules)
    (hV : ∀ V : T.Opens, IsAffineOpen V → ∀ q : ℕ,
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict (f ⁻¹ᵁ V).ι) q))
    (q : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M q) := by
  let U : T.affineOpens → T.Opens := fun V => V.1
  let W : T.affineOpens → X.Opens := fun V => f ⁻¹ᵁ U V
  have hU : iSup U = ⊤ := iSup_affineOpens_eq_top T
  have hW : iSup W = ⊤ := PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top f U hU
  apply AcyclicCoverTotalVanishing.IntrinsicCech.sheaf_cohomology_vanish_of_all_intersections
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) W hW
  intro p i n
  let V : T.Opens := ∏ᶜ fun k : Fin (p + 1) => U (i k)
  have hVaff : IsAffineOpen V := CechIntersections.affine_cechIntersection U (fun V => V.2) p i
  have heq : (∏ᶜ fun k : Fin (p + 1) => W (i k)) = f ⁻¹ᵁ V := by
    simp only [W, V, CechIntersections.opensProduct_eq_iInf]
    ext x
    change (x ∈ ⨅ k : Fin (p + 1), f ⁻¹ᵁ U (i k)) ↔
      f x ∈ ⨅ k : Fin (p + 1), U (i k)
    simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    rfl
  change Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
    (M.restrict (∏ᶜ fun k : Fin (p + 1) => W (i k)).ι) n)
  rw [heq]
  exact hV V hVaff n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseCoverVanishing

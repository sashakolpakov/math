import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineCohomologyVanishing

/-! # Base Ample Acyclicity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseAmpleAcyclicity

noncomputable section

/-! High ample powers are acyclic over any Noetherian affine scheme base, in genuine Ext cohomology. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem ample_lineBundle_eventually_acyclic_affine
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n → ∀ q : ℕ,
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.tensorPower n).sheaf (q + 1)) := by
  obtain ⟨B, hB⟩ := Ample.LineCohomologyVanishing.ample_lineBundle_eventually_vanish (f ≫ S.toSpecΓ) L hL
  exact ⟨B, fun n hn q ↦ ModuleCat.subsingleton_of_isZero (hB n hn q)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseAmpleAcyclicity

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoverRelativeAmpleAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicPushforwardCohomologyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.AmpleLine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.LineQuasicoherence

/-! # Ample Pushforward Acyclicity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow

noncomputable section

/-! High ample powers on the constructed Chow modification have acyclic coherent direct images on the original proper scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

theorem Modification.ChowModification.Model.amplePowerPushforward_eventually_acyclic
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f] (D : Modification.ChowModification.Model f) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n → ∀ q : ℕ,
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
        ((Scheme.Modules.pushforward D.projection).obj (D.ampleLineBundle.tensorPower n).sheaf) (q + 1)) := by
  have : IsProper D.projection := D.proper
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let U (i : ULift.{u} (Fin D.cover.n)) : X.Opens := D.cover.opens i.down
  have hUa (i : ULift.{u} (Fin D.cover.n)) : IsAffineOpen (U i) := D.cover.affine i.down
  have hU : ⨆ i, U i = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨i, hi⟩ := D.cover.covers x
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  obtain ⟨a, ha⟩ := Finite.CoverRelativeAmpleAcyclicity.finiteCover_relativelyAmple_eventually_acyclic D.projection
    D.ampleLineBundle D.ampleLineBundle_relative_to_target U hUa
  obtain ⟨b, hb⟩ := Ample.LineCohomologyVanishing.ample_lineBundle_eventually_vanish (D.projection ≫ f)
    D.ampleLineBundle D.ampleLineBundle_isAmple
  refine ⟨max a b, fun n hn q ↦ ?_⟩
  let L := D.ampleLineBundle.tensorPower n
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf (q + 1)) :=
    ModuleCat.subsingleton_of_isZero (hb n ((le_max_right a b).trans hn) q)
  exact (AcyclicPushforwardCohomologyComparison.pushforwardCohomologyAcyclicCoverEquiv D.projection L.sheaf
    U hU hUa (ha n ((le_max_left a b).trans hn)) q).injective.subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow

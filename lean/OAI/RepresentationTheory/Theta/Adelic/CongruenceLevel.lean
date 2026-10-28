import OAI.RepresentationTheory.Theta.Adelic.IntegralCompact

/-! # Congruence Level -/

namespace OAI.RepresentationTheory.Theta.Adelic.CongruenceLevel

noncomputable section

/-! Common compact open congruence levels for the actual finite Schwartz
action. All topological hypotheses are supplied by the concrete constructions. -/

open scoped _root_.NumberField _root_.Topology

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.CompactOpen OAI.RepresentationTheory.Theta.Adelic.IntegralCompact

theorem finite_family_congruence_level
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
    (n m : ℕ) (hN : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)
    (Φ : Finset (FiniteSchwartz.finiteSchwartz F (n * m))) (K₀ : OpenSubgroup (FiniteSchwartz.FiniteSU F H)) :
    ∃ L : OpenSubgroup (FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (FiniteSchwartz.FiniteSU F H)) ∧
      L ≤ K₀ ∧ ∀ f ∈ Φ, ∀ g ∈ L, FiniteSchwartz.finiteAction F H K hd C P D g f = f := by
  let U : Set (FiniteSchwartz.FiniteSU F H) := (K₀ : Set (FiniteSchwartz.FiniteSU F H)) ∩
    ⋂ f ∈ Φ, {g | FiniteSchwartz.finiteAction F H K hd C P D g f = f}
  have hU : IsOpen U := K₀.isOpen.inter
    (isOpen_biInter_finset fun f _ => FiniteSchwartz.finiteAction_smooth F H K hd C P D hN f)
  have h1 : (1 : FiniteSchwartz.FiniteSU F H) ∈ U := by
    refine ⟨K₀.one_mem, ?_⟩
    simp
  obtain ⟨L, hLc, hLU⟩ := CompactOpen.compact_open_subgroup_basis U (hU.mem_nhds h1)
  refine ⟨L, hLc, (fun g hg => (hLU hg).1), ?_⟩
  intro f hf g hg
  exact Set.mem_iInter₂.mp (hLU hg).2 f hf

end

end OAI.RepresentationTheory.Theta.Adelic.CongruenceLevel

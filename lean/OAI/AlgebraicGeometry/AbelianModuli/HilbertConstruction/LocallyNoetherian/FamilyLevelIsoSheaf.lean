import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoForget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.IsoSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.IsoCoveringSieveLocality

/-! # Family Level Iso Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FamilyLevelIsoSheaf

noncomputable section

/-! Complete polarized full-level isomorphisms between fixed locally Noetherian families satisfy Zariski descent on all test schemes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem familyLevelIsoFunctor_isSheaf_locallyNoetherian (hδ : ∀ i, 0 < δ i) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (Family.LevelIsoFunctor.familyLevelIsoFunctor A B) := by
  have hiso := Family.IsoSheaf.familyIsoFunctor_isSheaf_subcanonical A.abelian.scheme B.abelian.scheme
    Scheme.zariskiTopology
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro T R hR s hs
  obtain ⟨e, he, heu⟩ := (isSheaf_iff_isSheaf_of_type _ _).mp hiso R hR
    (s.map (Family.LevelIsoForget.familyLevelIsoForget A B)) (hs.map (Family.LevelIsoForget.familyLevelIsoForget A B))
  change (A.pullback T.hom).abelian.scheme ≅ (B.pullback T.hom).abelian.scheme at e
  have ha : ∀ {U : Over S} (c : U ⟶ T) (hc : R c),
      (s c hc).abelian.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c e.hom := by
    intro U c hc
    exact (congrArg Iso.hom (he c hc)).symm
  let a := Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_locallyNoetherian A B hδ T R hR e (fun c hc => s c hc) ha
  refine ⟨a, ?_, ?_⟩
  · intro U c hc
    apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
    exact (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B c a).trans
      ((congrArg (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c)
        (Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_locallyNoetherian_hom A B hδ T R hR e (fun c hc => s c hc) ha)).trans
        (ha c hc).symm)
  · intro b hb
    apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
    have hbe : b.abelian = e := by
      apply heu
      intro U c hc
      apply Iso.ext
      exact (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B c b).symm.trans
        (congrArg (fun z => z.abelian.hom) (hb c hc))
    exact (congrArg Iso.hom hbe).trans
      (Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_locallyNoetherian_hom A B hδ T R hR e (fun c hc => s c hc) ha).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FamilyLevelIsoSheaf

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoForget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.IsoSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoCoveringSieveLocality

/-! # Family Level Iso Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyLevelIsoSheaf

noncomputable section

/-! Complete isomorphisms from an arbitrary polarized family to a
pullback of a locally Noetherian family form a Zariski sheaf on all
test schemes. Only the target must admit the specified model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T)

theorem familyLevelIsoFunctor_isSheaf_modeledTarget :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over T) (Family.LevelIsoFunctor.familyLevelIsoFunctor B (A.pullback f)) := by
  have hiso := Family.IsoSheaf.familyIsoFunctor_isSheaf_subcanonical B.abelian.scheme (A.pullback f).abelian.scheme
    Scheme.zariskiTopology
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro V R hR s hs
  obtain ⟨e, he, heu⟩ := (isSheaf_iff_isSheaf_of_type _ _).mp hiso R hR
    (s.map (Family.LevelIsoForget.familyLevelIsoForget B (A.pullback f))) (hs.map (Family.LevelIsoForget.familyLevelIsoForget B (A.pullback f)))
  change (B.pullback V.hom).abelian.scheme ≅ ((A.pullback f).pullback V.hom).abelian.scheme at e
  have ha : ∀ {U : Over T} (c : U ⟶ V) (hc : R c),
      (s c hc).abelian.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c e.hom := by
    intro U c hc
    exact (congrArg Iso.hom (he c hc)).symm
  let a := Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget
    A f B V R hR e (fun c hc => s c hc) ha
  refine ⟨a, ?_, ?_⟩
  · intro U c hc
    apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
    exact (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom B (A.pullback f) c a).trans
      ((congrArg (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c)
        (Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget_hom
          A f B V R hR e (fun c hc => s c hc) ha)).trans (ha c hc).symm)
  · intro b hb
    apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
    have hbe : b.abelian = e := by
      apply heu
      intro U c hc
      apply Iso.ext
      exact (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom B (A.pullback f) c b).symm.trans
        (congrArg (fun z => z.abelian.hom) (hb c hc))
    exact (congrArg Iso.hom hbe).trans
      (Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_modeledTarget_hom
        A f B V R hR e (fun c hc => s c hc) ha).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyLevelIsoSheaf

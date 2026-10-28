import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.IsoFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSheaf

/-! # Iso Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.IsoSheaf

noncomputable section

/-! Actual isomorphisms between two fixed family pullbacks satisfy descent for every subcanonical topology. Forward maps and inverse maps glue, and their inverse equations are checked locally. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} (A B : Over S) (T : Over S) (R : Presieve T)

theorem familyMorphism_comp_eq_id_of_local
    (hA : Presieve.IsSeparatedFor (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor A A) R)
    (p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)
    (q : (Over.pullback T.hom).obj B ⟶ (Over.pullback T.hom).obj A)
    (h : ∀ {U : Over S} (c : U ⟶ T), R c →
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p ≫ Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c q = 𝟙 _) :
    p ≫ q = 𝟙 _ := by
  apply hA.ext
  intro U c hc
  change Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (p ≫ q) = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (𝟙 _)
  rw [Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_map_comp, IsoFunctor.geometricFamilyMorphismBaseChange_map_id]
  exact h c hc

theorem familyIso_isSheafFor
    (hAB : Presieve.IsSheafFor (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor A B) R)
    (hBA : Presieve.IsSheafFor (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor B A) R)
    (hAA : Presieve.IsSeparatedFor (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor A A) R)
    (hBB : Presieve.IsSeparatedFor (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor B B) R) :
    Presieve.IsSheafFor (IsoFunctor.familyIsoFunctor A B) R := by
  intro s hs
  obtain ⟨p, hp, hpu⟩ := hAB (s.map (IsoFunctor.familyIsoHom A B)) (hs.map (IsoFunctor.familyIsoHom A B))
  obtain ⟨q, hq, _⟩ := hBA (s.map (IsoFunctor.familyIsoInv A B)) (hs.map (IsoFunctor.familyIsoInv A B))
  change (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B at p
  change (Over.pullback T.hom).obj B ⟶ (Over.pullback T.hom).obj A at q
  have hpq : p ≫ q = 𝟙 _ := by
    apply familyMorphism_comp_eq_id_of_local A B T R hAA
    intro U c hc
    have hp' : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p = (s c hc).hom := hp c hc
    have hq' : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c q = (s c hc).inv := hq c hc
    rw [hp', hq']
    exact (s c hc).hom_inv_id
  have hqp : q ≫ p = 𝟙 _ := by
    apply familyMorphism_comp_eq_id_of_local B A T R hBB
    intro U c hc
    have hp' : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p = (s c hc).hom := hp c hc
    have hq' : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c q = (s c hc).inv := hq c hc
    rw [hp', hq']
    exact (s c hc).inv_hom_id
  refine ⟨⟨p, q, hpq, hqp⟩, ?_, ?_⟩
  · intro U c hc
    apply Iso.ext
    exact hp c hc
  · intro e he
    apply Iso.ext
    apply hpu
    intro U c hc
    exact congrArg Iso.hom (he c hc)

theorem familyIsoFunctor_isSheaf_subcanonical
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] :
    Presheaf.IsSheaf (J.over S) (IsoFunctor.familyIsoFunctor A B) := by
  have h (X Y : Over S) (T : Over S) (R : Sieve T) (hR : R ∈ (J.over S) T) :
      Presieve.IsSheafFor (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor X Y) R.arrows :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (MorphismSheaf.geometricFamilyMorphismFunctor_isSheaf_subcanonical X Y J) R hR
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro T R hR
  exact familyIso_isSheafFor A B T R.arrows (h A B T R hR) (h B A T R hR)
    (h A A T R hR).isSeparatedFor (h B B T R hR).isSeparatedFor

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.IsoSheaf

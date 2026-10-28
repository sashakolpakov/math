import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology

/-! # Complex Homology Composition -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyComposition.MappedComplexHomologyComposition

noncomputable section

/-! # Canonical homology transport commutes with composition of exact functors -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' u'' v''

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

local instance : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G
local instance : PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G

theorem shortComplex (S : ShortComplex C) :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  let d := S.homologyData.left
  let t : ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G)))
      ((d.map F).map G) (d.map (F ⋙ G)) := {
    φK := 𝟙 _
    φH := 𝟙 _
    commi := by
      change 𝟙 _ ≫ G.map (F.map d.i) = G.map (F.map d.i) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    commf' := by
      exact (Category.comp_id ((d.map F).map G).f').trans
        (((d.map F).map_f' G).trans
          ((congrArg G.map (d.map_f' F)).trans
            ((d.map_f' (F ⋙ G)).symm.trans (Category.id_comp (d.map (F ⋙ G)).f').symm)))
    commπ := by
      change G.map (F.map d.π) ≫ 𝟙 _ = 𝟙 _ ≫ G.map (F.map d.π)
      rw [Category.comp_id, Category.id_comp] }
  have ht : ((d.map F).map G).homologyIso.hom = (d.map (F ⋙ G)).homologyIso.hom := by
    have hc := t.homologyMap_comm
    rw [ShortComplex.homologyMap_id] at hc
    exact (Category.comp_id ((d.map F).map G).homologyIso.hom).symm.trans
      (hc.symm.trans (Category.id_comp (d.map (F ⋙ G)).homologyIso.hom))
  exact (LeftHomologyIso.MappedLeftHomologyIso.homologyIso G (S.map F) (d.map F)).trans ht

theorem complex (K : CochainComplex C ℕ) (n : ℕ) :
    (ComplexHomology.MappedComplexHomology.iso G ((F.mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫
        G.map (ComplexHomology.MappedComplexHomology.iso F K n).hom =
      (ComplexHomology.MappedComplexHomology.iso (F ⋙ G) K n).hom :=
  shortComplex F G (K.sc n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyComposition.MappedComplexHomologyComposition

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SchemeGluing
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over

/-! # Glued Sheaf Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GluedSheafSections

noncomputable section

/-! Compatible sections of a relative Zariski sheaf glue over an actual relative scheme gluing. The original overlap schemes are proved to be the intersections of its charts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} (D : CategoryTheory.GlueData.{u} (Over S))
variable (hD : ∀ i j, IsOpenImmersion (D.f i j).left)

theorem relativeGlueInclusion_isPullback (i j : D.J) :
    IsPullback (D.f i j) (D.t i j ≫ D.f j i)
      (SchemeGluing.relativeGlueInclusion D hD i) (SchemeGluing.relativeGlueInclusion D hD j) := by
  have : HasMulticoequalizer D.diagram := SchemeGluing.relativeGlueData_hasColimit D hD
  have : HasColimit (D.diagram.multispan ⋙ Over.forget S) := SchemeGluing.relativeGlueData_forget_hasColimit D hD
  exact IsPullback.of_isLimit (D.vPullbackConeIsLimitOfMap (Over.forget S) i j
    ((SchemeGluing.relativeSchemeGlueData D hD).vPullbackConeIsLimit i j))

theorem relativeGlueInclusion_sieve_mem :
    Sieve.ofArrows D.U (SchemeGluing.relativeGlueInclusion D hD) ∈
      (Scheme.zariskiTopology.over S) (SchemeGluing.relativeGlued D hD) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (SchemeGluing.relativeGlueOpenCover D hD).mem_grothendieckTopology

theorem relativeGlued_existsUnique_sheafSection
    (F : (Over S)ᵒᵖ ⥤ Type u) (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
    (s : ∀ i, F.obj (.op (D.U i)))
    (hs : ∀ i j, F.map (D.f i j).op (s i) = F.map (D.t i j ≫ D.f j i).op (s j)) :
    ∃! a : F.obj (.op (SchemeGluing.relativeGlued D hD)),
      ∀ i, F.map (SchemeGluing.relativeGlueInclusion D hD i).op a = s i := by
  have hf := (isSheaf_iff_isSheaf_of_type _ _).mp hF _ (relativeGlueInclusion_sieve_mem D hD)
  apply (Presieve.isSheafFor_arrows_iff _ _).mp ((Presieve.isSheafFor_iff_generate _).mpr hf) s
  intro i j T a b hab
  let p := relativeGlueInclusion_isPullback D hD i j
  let c := p.lift a b hab
  have ha : c ≫ D.f i j = a := p.lift_fst a b hab
  have hb : c ≫ (D.t i j ≫ D.f j i) = b := p.lift_snd a b hab
  calc
    F.map a.op (s i) = F.map c.op (F.map (D.f i j).op (s i)) :=
      (congrArg (fun k => F.map k.op (s i)) ha.symm).trans
        (F.map_comp_apply (D.f i j).op c.op (s i))
    _ = F.map c.op (F.map (D.t i j ≫ D.f j i).op (s j)) := congrArg (F.map c.op) (hs i j)
    _ = F.map b.op (s j) :=
      (F.map_comp_apply (D.t i j ≫ D.f j i).op c.op (s j)).symm.trans
        (congrArg (fun k => F.map k.op (s j)) hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GluedSheafSections

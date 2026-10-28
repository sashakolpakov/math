import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction

/-! # Base Section Vector Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVectorChange.Constructions

noncomputable section

/-! Actual section vectors and their stalk equations are unchanged
when passing to a smaller algebraic base containing the chosen point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y Z N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom] [IsIntegral N.left] [Smooth N.hom]
  (j : Y ⟶ N) (j' : Z ⟶ N) [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  (k : Z ⟶ Y) (hk : k ≫ j = j') (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hU' : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j'))
  (n : ℕ) (s : Fin n → Γ(Y.left, ⊤))

include hk in
theorem baseSectionVector_change :
    BaseSectionVector.Constructions.baseSectionVector j' U hU' n (fun i => k.left.appTop (s i)) = BaseSectionVector.Constructions.baseSectionVector j U hU n s := by
  ext x : 1
  funext i
  exact BaseSectionChange.Constructions.baseSectionEvaluation_change j j' k hk U hU hU' (s i) x

include hk in
theorem relativeCohomologyMap_vector_change (A : Set U)
    (hf : Set.MapsTo (BaseSectionVector.Constructions.baseSectionVector j' U hU' n (fun i => k.left.appTop (s i))) A ({0}ᶜ))
    (hg : Set.MapsTo (BaseSectionVector.Constructions.baseSectionVector j U hU n s) A ({0}ᶜ)) (d : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector j' U hU' n (fun i => k.left.appTop (s i))) hf d =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector j U hU n s) hg d :=
  ThomOpenRestriction.Constructions.pairMap_congr (baseSectionVector_change j j' k hk U hU hU' n s) hf hg d

theorem section_stalk_restrict (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B C : V.carrier.Opens) (hCB : C ≤ B)
    (x : V.carrier) (hxC : x ∈ C) (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    V.carrier.presheaf.germ C x hxC (C.topIso.hom ((V.carrier.homOfLE hCB).appTop s)) =
      V.carrier.presheaf.germ B x (hCB hxC) (B.topIso.hom s) := by
  rw [Section.BaseRestriction.Constructions.topIso_sectionRestriction B C hCB s]
  exact V.carrier.presheaf.germ_res_apply (homOfLE hCB) x hxC (B.topIso.hom s)

theorem section_list_stalk_restrict (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B C : V.carrier.Opens) (hCB : C ≤ B)
    (x : V.carrier) (hxC : x ∈ C) (s : List Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    (s.map (V.carrier.homOfLE hCB).appTop).map (fun a => V.carrier.presheaf.germ C x hxC (C.topIso.hom a)) =
      s.map (fun a => V.carrier.presheaf.germ B x (hCB hxC) (B.topIso.hom a)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  exact section_stalk_restrict V B C hCB x hxC a

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVectorChange.Constructions

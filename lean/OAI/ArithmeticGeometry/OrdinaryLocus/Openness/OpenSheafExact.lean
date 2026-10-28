import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenSheafInjectives

/-! # Open Sheaf Exact -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenSheafExact.Construction

noncomputable section

/-! Exactness of restriction of abelian sheaves to open subspaces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X : TopCat.{u}} (U : Opens X)

instance openAbelianRestrict_isLeftAdjoint :
    (U.sheafRestrict (C := AddCommGrpCat.{u})).IsLeftAdjoint := by
  let j : TopCat.of U ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hj : Topology.IsOpenEmbedding j := U.isOpenEmbedding
  have hcont : hj.isOpenMap.functor.IsContinuous
      (_root_.Opens.grothendieckTopology U) (_root_.Opens.grothendieckTopology X) :=
    hj.functor_isContinuous
  have hright : (Opens.map j).IsContinuous
      (_root_.Opens.grothendieckTopology X) (_root_.Opens.grothendieckTopology U) := by
    apply Functor.isContinuous_of_coverPreserving
    · exact compatiblePreserving_opens_map j
    · exact coverPreserving_opens_map j
  exact (hj.isOpenMap.adjunction.sheafPushforwardContinuous
    (E := AddCommGrpCat.{u}) (_root_.Opens.grothendieckTopology U)
    (_root_.Opens.grothendieckTopology X)).isLeftAdjoint

theorem openAbelianRestrict_preservesFiniteColimits :
    PreservesFiniteColimits (U.sheafRestrict (C := AddCommGrpCat.{u})) := inferInstance

theorem openAbelianRestrict_shortExact
    (S : ShortComplex (AbelianSheafInjectives.Construction.AbelianSheaves X)) (hS : S.ShortExact) :
    (S.map (U.sheafRestrict (C := AddCommGrpCat.{u}))).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  exact hS.map _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenSheafExact.Construction

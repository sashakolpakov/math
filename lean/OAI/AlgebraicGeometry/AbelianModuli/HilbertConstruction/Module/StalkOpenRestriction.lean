import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ComplexLocalExactness

/-! # Stalk Open Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkOpenRestriction

noncomputable section

/-! Exactness at the actual local-ring stalk is unchanged on passing
to an open neighborhood. This uses the natural additive stalk
comparison and faithful forgetting of the local scalar action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

attribute [local instance] StalkExactness.moduleStalkUnderlying_additive
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance stalkOpenPullbackAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _

theorem moduleShortComplex_stalk_exact_iff_additive
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (x : X) :
    (S.map (StalkExactness.moduleStalkFunctor x)).Exact ↔
      (S.map (Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact := by
  rw [(S.map (StalkExactness.moduleStalkFunctor x)).exact_iff_exact_map_forget₂]
  exact ShortComplex.exact_iff_of_iso (S.mapNatIso (StalkExactness.moduleStalkForgetIso x))

theorem moduleShortComplex_pullback_stalk_exact_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (S : ShortComplex X.Modules) (y : Y) :
    ((S.map (Scheme.Modules.pullback f)).map (StalkExactness.moduleStalkFunctor y)).Exact ↔
      (S.map (StalkExactness.moduleStalkFunctor (f y))).Exact := by
  rw [moduleShortComplex_stalk_exact_iff_additive,
    moduleShortComplex_stalk_exact_iff_additive]
  let G := Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let e : Scheme.Modules.pullback f ⋙ G ≅
      Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f y) :=
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback f).symm G ≪≫
      Scheme.Modules.restrictStalkNatIso f y
  exact ShortComplex.exact_iff_of_iso (S.mapNatIso e)

theorem moduleCochain_exactAt_iff_stalk
    {X : Scheme.{u}} (C : CochainComplex X.Modules ℤ) (i : ℤ) :
    C.ExactAt i ↔ ∀ x : X,
      (((StalkExactness.moduleStalkFunctor x).mapHomologicalComplex (.up ℤ)).obj C).ExactAt i :=
  StalkExactness.moduleShortComplex_exact_iff_stalk (C.sc i)

theorem moduleCochain_pullback_stalk_exactAt_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (C : CochainComplex X.Modules ℤ) (y : Y) (i : ℤ) :
    (((StalkExactness.moduleStalkFunctor y).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj C)).ExactAt i ↔
      (((StalkExactness.moduleStalkFunctor (f y)).mapHomologicalComplex (.up ℤ)).obj C).ExactAt i :=
  moduleShortComplex_pullback_stalk_exact_iff f (C.sc i) y

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkOpenRestriction

import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafComplexLift

/-! # Singular Sheaf Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions

noncomputable section

/-! Ordinary singular pullback induces a genuine map to the source's pushforward sheaf complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
variable {X Y : TopCat.{0}} (f : Y ⟶ X)

def openPreimageMap (U : Opens X) : TopCat.of ((Opens.map f).obj U) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun y => ⟨f y.val, y.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem openPreimageMap_naturality {U W : Opens X} (i : U ⟶ W) :
    openPreimageMap f U ≫ (Opens.toTopCat X).map i =
      (Opens.toTopCat Y).map ((Opens.map f).map i) ≫ openPreimageMap f W := rfl

theorem singularOpenPreimagePullback_naturality {U W : Opens X} (i : U ⟶ W) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat X).map i) ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (openPreimageMap f U) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (openPreimageMap f W) ≫
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat Y).map ((Opens.map f).map i)) := by
  rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, openPreimageMap_naturality]

def singularOpenPreimageSheafMap (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (TopCat.of U) ⟶ AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSections M Y ((Opens.map f).obj U) :=
  AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (openPreimageMap f U) ≫
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M Y ((Opens.map f).obj U)

theorem singularOpenPreimageSheafMap_naturality {U W : Opens X} (i : U ⟶ W) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat X).map i) ≫ singularOpenPreimageSheafMap M f U =
      singularOpenPreimageSheafMap M f W ≫
        AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSectionsRestriction M Y ((Opens.map f).map i) := by
  unfold singularOpenPreimageSheafMap
  rw [← Category.assoc, singularOpenPreimagePullback_naturality, Category.assoc,
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections_naturality, ← Category.assoc]

instance sheafPushforward_additive : (TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).Additive where
  map_add := rfl

def singularPushforwardSheafComplex : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ :=
  ((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M Y))

def singularSheafPullbackPresheafMap : AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X ⟶
    AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex (singularPushforwardSheafComplex M f) where
  f n :=
    { app U := (singularOpenPreimageSheafMap M f U.unop).f n
      naturality U W i := congrArg (fun g => g.f n)
        (singularOpenPreimageSheafMap_naturality M f i.unop) }
  comm' i j hij := by
    apply NatTrans.ext
    funext U
    exact (singularOpenPreimageSheafMap M f U.unop).comm' i j hij

def singularSheafPullbackMap :
    AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) ⟶ singularPushforwardSheafComplex M f :=
  SheafComplexLift.Constructions.sheafComplexLift (singularSheafPullbackPresheafMap M f)

theorem singularSheafPullbackMap_unit (U : Opens X) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M X U).f n ≫
        ((singularSheafPullbackMap M f).f n).hom.app (op U) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (openPreimageMap f U)).f n ≫
        (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M Y ((Opens.map f).obj U)).f n :=
  NatTrans.congr_app (SheafComplexLift.Constructions.sheafComplexLift_unit (singularSheafPullbackPresheafMap M f) n) (op U)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions

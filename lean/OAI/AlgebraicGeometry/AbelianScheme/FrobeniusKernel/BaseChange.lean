import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange.Construction

noncomputable section

/-!
Actual fppf quotient sheaves and arbitrary specialization. The base-change
functor is restriction on the big fppf sites. Its preservation of quotients
is proved using the continuous/cocontinuous adjunction, including for a
closed residue-field immersion. No reducedness or constant-group condition
is imposed on either member of the relation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

local instance pulledBackGroup {S T : Scheme.{u}} (f : T ⟶ S)
    (A : Over S) [GrpObj A] : GrpObj ((Over.pullback f).obj A) :=
  Functor.grpObjObj (F := Over.pullback f) (G := A)

abbrev FppfSheaves (S : Scheme.{u}) :=
  Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))

/-- The genuine functor of points, retaining sections on nonreduced schemes. -/
abbrev fppfPoints (S : Scheme.{u}) : Over S ⥤ FppfSheaves S :=
  (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}

/-- Restriction from S-schemes to T-schemes along an arbitrary base map. -/
abbrev fppfBaseChange {S T : Scheme.{u}} (f : T ⟶ S) :
    FppfSheaves S ⥤ FppfSheaves T :=
  Scheme.fppfTopology.overMapPullback (Type (u + 1)) f

instance fppfBaseChange_isLeftAdjoint {S T : Scheme.{u}} (f : T ⟶ S) :
    (fppfBaseChange f).IsLeftAdjoint :=
  ((Over.map f).sheafAdjunctionCocontinuous (Type (u + 1))
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)).isLeftAdjoint

instance fppfBaseChange_preservesColimits {S T : Scheme.{u}} (f : T ⟶ S) :
    PreservesColimits (fppfBaseChange f) := inferInstance

/-- Restricting a representable sheaf gives the sheaf of the actual scheme
pullback. This is the pullback universal property on every test scheme. -/
def fppfBaseChangePointsIso {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) :
    (fppfBaseChange f).obj ((fppfPoints S).obj A) ≅
      (fppfPoints T).obj ((Over.pullback f).obj A) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso <|
    NatIso.ofComponents
      (fun X => (Equiv.ulift.trans
        ((Over.mapPullbackAdj f).homEquiv X.unop A) |>.trans Equiv.ulift.symm).toIso)
      (by
        intro X Y g
        ext a
        apply ULift.ext
        exact (Over.mapPullbackAdj f).homEquiv_naturality_left g.unop a.down)

theorem fppfBaseChangePointsIso_naturality {S T : Scheme.{u}} (f : T ⟶ S)
    {A B : Over S} (a : A ⟶ B) :
    (fppfBaseChange f).map ((fppfPoints S).map a) ≫
        (fppfBaseChangePointsIso f B).hom =
      (fppfBaseChangePointsIso f A).hom ≫
        (fppfPoints T).map ((Over.pullback f).map a) := by
  apply Sheaf.hom_ext
  ext X x
  apply ULift.ext
  exact (Over.mapPullbackAdj f).homEquiv_naturality_right x.down a

/-- The sheaf quotient of a scheme relation. For a subgroup action the two
maps are translation and projection H x A -> A. -/
def relationQuotient {S : Scheme.{u}} {R A : Over S} (r₁ r₂ : R ⟶ A) :
    FppfSheaves S :=
  coequalizer ((fppfPoints S).map r₁) ((fppfPoints S).map r₂)

def relationQuotientProjection {S : Scheme.{u}} {R A : Over S}
    (r₁ r₂ : R ⟶ A) : (fppfPoints S).obj A ⟶ relationQuotient r₁ r₂ :=
  coequalizer.π _ _

/-- Construction of a quotient in characteristic q requires no choice of
an etale presentation of the subgroup. -/
def subgroupQuotient {S : Scheme.{u}} {A H : Over S} [GrpObj A]
    (i : H ⟶ A) : FppfSheaves S :=
  relationQuotient ((fst H A ≫ i) * snd H A) (snd H A)

/-- Specialization commutes with the constructed coequalizer as a sheaf.
The map is the canonical colimit comparison, not an assumed isomorphism. -/
def relationQuotientSpecialization {S T : Scheme.{u}} (f : T ⟶ S)
    {R A : Over S} (r₁ r₂ : R ⟶ A) :
    (fppfBaseChange f).obj (relationQuotient r₁ r₂) ≅
      coequalizer ((fppfBaseChange f).map ((fppfPoints S).map r₁))
        ((fppfBaseChange f).map ((fppfPoints S).map r₂)) :=
  (PreservesCoequalizer.iso (fppfBaseChange f)
    ((fppfPoints S).map r₁) ((fppfPoints S).map r₂)).symm

/-- The comparison preserves the quotient map itself. -/
theorem relationQuotientSpecialization_projection {S T : Scheme.{u}}
    (f : T ⟶ S) {R A : Over S} (r₁ r₂ : R ⟶ A) :
    (fppfBaseChange f).map (relationQuotientProjection r₁ r₂) ≫
        (relationQuotientSpecialization f r₁ r₂).hom =
      coequalizer.π ((fppfBaseChange f).map ((fppfPoints S).map r₁))
        ((fppfBaseChange f).map ((fppfPoints S).map r₂)) := by
  exact map_π_preserves_coequalizer_inv (fppfBaseChange f)
    ((fppfPoints S).map r₁) ((fppfPoints S).map r₂)

/-- Specialization is the quotient of the base-changed *schemes* and maps,
not merely the quotient of unnamed sheaves. Both canonical comparisons
are constructed from universal properties. -/
def relationQuotientBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S)
    {R A : Over S} (r₁ r₂ : R ⟶ A) :
    (fppfBaseChange f).obj (relationQuotient r₁ r₂) ≅
      relationQuotient ((Over.pullback f).map r₁) ((Over.pullback f).map r₂) :=
  (relationQuotientSpecialization f r₁ r₂).trans <|
    HasColimit.isoOfNatIso (parallelPairIso
      ((fppfBaseChange f).map ((fppfPoints S).map r₁))
      ((fppfBaseChange f).map ((fppfPoints S).map r₂))
      ((fppfPoints T).map ((Over.pullback f).map r₁))
      ((fppfPoints T).map ((Over.pullback f).map r₂))
      (fppfBaseChangePointsIso f R) (fppfBaseChangePointsIso f A)
      (fppfBaseChangePointsIso_naturality f r₁)
      (fppfBaseChangePointsIso_naturality f r₂))

theorem baseChange_translation {S T : Scheme.{u}} (f : T ⟶ S)
    {A H : Over S} [GrpObj A] (i : H ⟶ A) :
    (Functor.Monoidal.μIso (Over.pullback f) H A).hom ≫
        (Over.pullback f).map ((fst H A ≫ i) * snd H A) =
      (fst ((Over.pullback f).obj H) ((Over.pullback f).obj A) ≫
        (Over.pullback f).map i) *
      snd ((Over.pullback f).obj H) ((Over.pullback f).obj A) := by
  rw [(Over.pullback f).map_mul, MonObj.comp_mul, (Over.pullback f).map_comp]
  simp only [← Category.assoc, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd]

/-- The specialized quotient is the quotient by the actual specialized
subgroup action. Product coherence identifies the pulled-back relation
with H_T x A_T acting on A_T. -/
def subgroupQuotientBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S)
    {A H : Over S} [GrpObj A] (i : H ⟶ A) :
    (fppfBaseChange f).obj (subgroupQuotient i) ≅
      subgroupQuotient ((Over.pullback f).map i) := by
  let F := Over.pullback f
  let p := Functor.Monoidal.μIso F H A
  let act := (fst H A ≫ i) * snd H A
  let act' := (fst (F.obj H) (F.obj A) ≫ F.map i) * snd (F.obj H) (F.obj A)
  have ha : F.map act = p.inv ≫ act' := by
    apply (cancel_epi p.hom).mp
    rw [← Category.assoc, p.hom_inv_id, Category.id_comp]
    exact baseChange_translation f i
  have hp : F.map (snd H A) = p.inv ≫ snd (F.obj H) (F.obj A) := by
    apply (cancel_epi p.hom).mp
    rw [← Category.assoc, p.hom_inv_id, Category.id_comp]
    exact Functor.Monoidal.μ_snd F H A
  refine (relationQuotientBaseChangeIso f act (snd H A)).trans ?_
  apply HasColimit.isoOfNatIso
  apply parallelPairIso _ _ _ _ ((fppfPoints T).mapIso p.symm) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom,
      ← Functor.map_comp] using congrArg (fppfPoints T).map ha
  · simpa only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom,
      ← Functor.map_comp] using congrArg (fppfPoints T).map hp

/-- The quotient is constructed by the universal property on all fppf
sheaves, hence in particular on the functors represented by schemes. -/
theorem relationQuotient_universal {S : Scheme.{u}} {R A : Over S}
    (r₁ r₂ : R ⟶ A) (Q : FppfSheaves S)
    (a : (fppfPoints S).obj A ⟶ Q)
    (ha : (fppfPoints S).map r₁ ≫ a = (fppfPoints S).map r₂ ≫ a) :
    ∃! b : relationQuotient r₁ r₂ ⟶ Q,
      relationQuotientProjection r₁ r₂ ≫ b = a := by
  refine ⟨coequalizer.desc a ha, coequalizer.π_desc a ha, ?_⟩
  intro b hb
  apply coequalizer.hom_ext
  exact hb.trans (coequalizer.π_desc a ha).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange.Construction

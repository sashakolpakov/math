import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange

/-! # Test Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction

noncomputable section

/-!
Every original test scheme with a parameter point is canonically a test
scheme over the parameter. The point and subgroup comparisons are
faithful, including on nonreduced tests.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

def parameterTest {S : Scheme.{u}} {P X : Over S} (t : X ⟶ P) : Over P.left := Over.mk t.left

def parameterTestIso {S : Scheme.{u}} {P X : Over S} (t : X ⟶ P) :
    (Over.map P.hom).obj (parameterTest t) ≅ X :=
  Over.isoMk (Iso.refl _) ((Category.id_comp X.hom).trans t.w.symm)

theorem parameterTestIso_hom_base {S : Scheme.{u}} {P X : Over S} (t : X ⟶ P) :
    (parameterTestIso t).hom ≫ t = Relative.ParameterBaseChange.Construction.parameterBasePoint P (parameterTest t) :=
  Over.OverMorphism.ext (Category.id_comp t.left)

theorem parameterTestIso_inv_base {S : Scheme.{u}} {P X : Over S} (t : X ⟶ P) :
    (parameterTestIso t).inv ≫ Relative.ParameterBaseChange.Construction.parameterBasePoint P (parameterTest t) = t :=
  Over.OverMorphism.ext (Category.id_comp t.left)

theorem relativeSubgroup_membership_iso {S : Scheme.{u}} {A P X Y : Over S} [GrpObj A]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (e : X ≅ Y) (t : Y ⟶ P) (x : Y ⟶ A) :
    e.hom ≫ x ∈ F.points X (e.hom ≫ t) ↔ x ∈ F.points Y t := by
  constructor
  · intro h
    have hh := F.naturality e.inv (e.hom ≫ t) h
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hh
  · exact F.naturality e.hom t

def parameterizePoint {S : Scheme.{u}} (G : Grp (Over S)) {P X : Over S}
    (t : X ⟶ P) (x : X ⟶ G.X) :
    parameterTest t ⟶ ((Over.pullback P.hom).mapGrp.obj G).X :=
  CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (parameterTest t) ((parameterTestIso t).hom ≫ x)

theorem parameterizePoint_membership {S : Scheme.{u}} (G : Grp (Over S)) {P X : Over S}
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (t : X ⟶ P) (x : X ⟶ G.X)
    (b : parameterTest t ⟶ Over.mk (𝟙 P.left)) :
    parameterizePoint G t x ∈ (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F).points (parameterTest t) b ↔
      x ∈ F.points X t := by
  change (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (parameterTest t)).symm
      (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (parameterTest t) ((parameterTestIso t).hom ≫ x)) ∈
        F.points _ (Relative.ParameterBaseChange.Construction.parameterBasePoint P (parameterTest t)) ↔ _
  rw [MulEquiv.symm_apply_apply, ← parameterTestIso_hom_base]
  exact relativeSubgroup_membership_iso F (parameterTestIso t) t x

theorem relativeSubgroupOverParameter_injective {S : Scheme.{u}} (G : Grp (Over S)) (P : Over S) :
    Function.Injective (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P) := by
  intro F H h
  ext X t x
  let b : parameterTest t ⟶ Over.mk (𝟙 P.left) := Over.homMk t.left (Category.comp_id _)
  rw [← parameterizePoint_membership G F t x b, ← parameterizePoint_membership G H t x b, h]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction

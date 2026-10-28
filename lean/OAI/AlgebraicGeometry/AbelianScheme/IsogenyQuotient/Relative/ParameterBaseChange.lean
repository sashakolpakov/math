import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeValues

/-! # Parameter Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction

noncomputable section

/-!
Regard an actual relative subgroup family over its parameter scheme.
Its sections are defined using the ordinary pullback point equivalence
and the original subgroup membership predicate, on every test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

def parameterBasePoint {S : Scheme.{u}} (P : Over S) (U : Over P.left) :
    (Over.map P.hom).obj U ⟶ P := Over.homMk U.hom rfl

theorem parameterBasePoint_natural {S : Scheme.{u}} (P : Over S)
    {U V : Over P.left} (g : V ⟶ U) :
    (Over.map P.hom).map g ≫ parameterBasePoint P U = parameterBasePoint P V :=
  Over.OverMorphism.ext g.w

theorem pullbackPointMulEquiv_symm_natural {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) {U V : Over T} (g : V ⟶ U)
    (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G V).symm (g ≫ x) =
      (Over.map f).map g ≫ (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x := by
  apply Over.OverMorphism.ext
  exact Category.assoc g.left x.left (CategoryTheory.Limits.pullback.fst G.X.hom f)

def relativeSubgroupOverParameter {S : Scheme.{u}} (G : Grp (Over S)) (P : Over S)
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).mapGrp.obj G).X (Over.mk (𝟙 P.left)) where
  points U _ := (F.points ((Over.map P.hom).obj U) (parameterBasePoint P U)).comap
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.toMonoidHom
  naturality := by
    intro V U g t x hx
    change (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G V).symm (g ≫ x) ∈
      F.points ((Over.map P.hom).obj V) (parameterBasePoint P V)
    have h := F.naturality ((Over.map P.hom).map g) (parameterBasePoint P U) hx
    rw [parameterBasePoint_natural] at h
    exact (pullbackPointMulEquiv_symm_natural P.hom G g x).symm ▸ h

theorem relativeSubgroupOverParameter_membership {S : Scheme.{u}}
    (G : Grp (Over S)) (P : Over S) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P)
    (U : Over P.left) (t : U ⟶ Over.mk (𝟙 P.left))
    (x : U ⟶ ((Over.pullback P.hom).mapGrp.obj G).X) :
    x ∈ (relativeSubgroupOverParameter G P F).points U t ↔
      (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x ∈
        F.points ((Over.map P.hom).obj U) (parameterBasePoint P U) := Iff.rfl

theorem relativeSubgroupOverParameter_killed {S : Scheme.{u}}
    (G : Grp (Over S)) (P : Over S) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P)
    (n : ℕ) (h : F.KilledBy n) : (relativeSubgroupOverParameter G P F).KilledBy n := by
  intro U t x hx
  apply (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.injective
  exact (map_pow (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x n).trans
    ((h _ _ _ hx).trans (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.map_one.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction

import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangePoints

/-! # Subgroup Choice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupChoice.Construction

noncomputable section

/-! An original subgroup choice becomes a subgroup choice on the actual
pulled-back abelian scheme over its parameter, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def subgroupComapMulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (J : Subgroup H) :
    J.comap e.toMonoidHom ≃* J where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by
    change e (e.symm y.val) ∈ J
    rw [e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)

def subgroupChoiceOverParameter {S : Scheme.{0}} (G : Grp (Over S)) (P : Over S)
    (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (F : TorsionQuotient.SubgroupFunctor.SubgroupChoice G.X n M P) :
    TorsionQuotient.SubgroupFunctor.SubgroupChoice ((Over.pullback P.hom).mapGrp.obj G).X n M (Over.mk (𝟙 P.left)) where
  subgroup := Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F.subgroup
  killed := Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter_killed G P F.subgroup n F.killed
  moduleType := by
    intro k _ _ s _
    let e := (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk s)).symm
    let J := F.subgroup.points (Over.mk (s ≫ P.hom)) (Over.homMk s rfl)
    obtain ⟨m⟩ := F.moduleType k (s ≫ P.hom) (Over.homMk s rfl)
    exact ⟨(subgroupComapMulEquiv e J).trans m⟩
  geometric := F.geometric.elim fun R => ⟨SubgroupModel.Construction.relativeSubgroupOverParameter_model G P F.subgroup R⟩

set_option backward.isDefEq.respectTransparency false in
def supportedChoiceOverParameter {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (P : Over S) (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (p : A.scheme ⟶ A.scheme) [IsMonHom p] (F : SubgroupFunctor.Construction.SupportedChoice A.scheme n M p P) :
    SubgroupFunctor.Construction.SupportedChoice (A.pullback P.hom).scheme n M ((Over.pullback P.hom).map p) (Over.mk (𝟙 P.left)) := by
  refine ⟨subgroupChoiceOverParameter (Grp.mk A.scheme) P n M F.val, ?_⟩
  intro U t x hx
  apply (A.baseChangePointsMulEquiv P.hom U).injective
  exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map p P.hom U x).trans
    (F.property ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U)
      (A.baseChangePointsMulEquiv P.hom U x) hx)

theorem supportedChoiceOverParameter_membership
    {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (P : Over S) (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (p : A.scheme ⟶ A.scheme) [IsMonHom p] (F : SubgroupFunctor.Construction.SupportedChoice A.scheme n M p P)
    (U : Over P.left) (t : U ⟶ Over.mk (𝟙 P.left)) (x : U ⟶ (A.pullback P.hom).scheme) :
    x ∈ (supportedChoiceOverParameter A P n M p F).val.subgroup.points U t ↔
      A.baseChangePointsMulEquiv P.hom U x ∈
        F.val.subgroup.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U) := Iff.rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupChoice.Construction

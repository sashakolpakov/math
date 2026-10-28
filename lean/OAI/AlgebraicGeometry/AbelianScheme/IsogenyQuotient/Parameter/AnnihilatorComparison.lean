import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison

/-! # Annihilator Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison.Construction

noncomputable section

/-!
The annihilator of the original relative family agrees, on every test
scheme, with the annihilator after passage to the parameter scheme.
Every test over the original base is retained through its induced
parameter point; the comparison uses the original scheme pairing.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative

universe u

def parameterTestMap {S : Scheme.{u}} (P : Over S) {U : Over P.left} {X : Over S}
    (f : X ⟶ (Over.map P.hom).obj U) :
    TestComparison.Construction.parameterTest (f ≫ Relative.ParameterBaseChange.Construction.parameterBasePoint P U) ⟶ U := Over.homMk f.left rfl

theorem parameterTestMap_original {S : Scheme.{u}} (P : Over S) {U : Over P.left} {X : Over S}
    (f : X ⟶ (Over.map P.hom).obj U) :
    (Over.map P.hom).map (parameterTestMap P f) =
      (TestComparison.Construction.parameterTestIso (f ≫ Relative.ParameterBaseChange.Construction.parameterBasePoint P U)).hom ≫ f :=
  Over.OverMorphism.ext (Category.id_comp f.left).symm

variable {S : Scheme.{u}} (G K : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj K.X]
  (P : Over S) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P)
  (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := K.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem relativeParameter_annihilator_comparison :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter K P (e.relativeAnnihilator F) =
      (PairingBaseChange.Construction.nativePairingPullback P.hom G K e).relativeAnnihilator (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) := by
  ext U b y
  constructor
  · intro hy V g x hx
    apply (PairingBaseChangeValues.Construction.nativePairingPullback_eq_one_iff P.hom G K e V x (g ≫ y)).mpr
    have hmem : (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G V).symm x ∈
        F.points ((Over.map P.hom).obj V) ((Over.map P.hom).map g ≫ Relative.ParameterBaseChange.Construction.parameterBasePoint P U) :=
      (Relative.ParameterBaseChange.Construction.parameterBasePoint_natural P g).symm ▸ hx
    have hval := hy ((Over.map P.hom).obj V) ((Over.map P.hom).map g)
      ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G V).symm x) hmem
    exact (congrArg (e.pairValue ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G V).symm x))
      (Relative.ParameterBaseChange.Construction.pullbackPointMulEquiv_symm_natural P.hom K g y)).trans hval
  · intro hy X f x hx
    let t := f ≫ Relative.ParameterBaseChange.Construction.parameterBasePoint P U
    let V := TestComparison.Construction.parameterTest t
    let g : V ⟶ U := parameterTestMap P f
    let z := TestComparison.Construction.parameterizePoint G t x
    have hz : z ∈ (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F).points V (g ≫ b) :=
      (TestComparison.Construction.parameterizePoint_membership G F t x (g ≫ b)).mpr hx
    have hvalue := (PairingBaseChangeValues.Construction.nativePairingPullback_eq_one_iff P.hom G K e V z (g ≫ y)).mp (hy V g z hz)
    have hfirst : (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G V).symm z = (TestComparison.Construction.parameterTestIso t).hom ≫ x :=
      (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G V).symm_apply_apply _
    have hsecond : (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom K V).symm (g ≫ y) =
        (TestComparison.Construction.parameterTestIso t).hom ≫ (f ≫ (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom K U).symm y) :=
      (Relative.ParameterBaseChange.Construction.pullbackPointMulEquiv_symm_natural P.hom K g y).trans
        ((congrArg (fun k => k ≫ (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom K U).symm y)
          (parameterTestMap_original P f)).trans (Category.assoc _ _ _))
    have hn := e.pairValue_natural (TestComparison.Construction.parameterTestIso t).hom x
      (f ≫ (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom K U).symm y)
    have hh : (TestComparison.Construction.parameterTestIso t).hom ≫
        e.pairValue x (f ≫ (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom K U).symm y) = 1 :=
      hn.symm.trans ((congrArg₂ e.pairValue hfirst hsecond).symm.trans hvalue)
    exact (cancel_epi (TestComparison.Construction.parameterTestIso t).hom).mp
      (hh.trans (MonObj.comp_one (TestComparison.Construction.parameterTestIso t).hom).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison.Construction

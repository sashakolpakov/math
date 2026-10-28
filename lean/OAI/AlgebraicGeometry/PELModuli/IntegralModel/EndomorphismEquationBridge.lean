import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicGroupHomEquations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismHom

/-! # Endomorphism Equation Bridge -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismEquationBridge.EndomorphismFamilies

noncomputable section

/-! Identify the closed group equations with the actual geometric
endomorphism ring used by integral PEL actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem nativeHomEquiv_eq_relative (T : Over S)
    (r : (A.pullback T.hom).scheme ⟶ (A.pullback T.hom).scheme) :
    IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv A.scheme A.scheme T r = EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T r := rfl

theorem relativeHom_group_equations (T : Over S) (r : Finite.Actions.GroupEndRing (A.pullback T.hom)) :
    Group.HomEquations.GroupHomEquations.RespectsGroup A.scheme (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T (r.hom (A.pullback T.hom))) := by
  rw [← nativeHomEquiv_eq_relative]
  let q : (Over.pullback T.hom).obj A.scheme ⟶ (Over.pullback T.hom).obj A.scheme :=
    r.hom (A.pullback T.hom)
  have : IsMonHom q := inferInstanceAs (IsMonHom (r.hom (A.pullback T.hom)))
  exact IntrinsicGroupHomEquations.GroupHomEquations.native_group_equations_of_isMonHom A.scheme T q

def groupEndOfFamily (T : Over S) (f : T ⨯ A.scheme ⟶ A.scheme)
    (hf : Group.HomEquations.GroupHomEquations.RespectsGroup A.scheme f) : Finite.Actions.GroupEndRing (A.pullback T.hom) := by
  let r : (A.pullback T.hom).scheme ⟶ (A.pullback T.hom).scheme := (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T).symm f
  have hEq : Group.HomEquations.GroupHomEquations.RespectsGroup A.scheme
      (IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv A.scheme A.scheme T r) := by
    rw [nativeHomEquiv_eq_relative]
    exact ((EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T).apply_symm_apply f).symm ▸ hf
  have : IsMonHom r := IntrinsicGroupHomPoints.GroupHomEquations.native_isMonHom_of_group_equations A.scheme T r hEq
  exact Finite.Actions.GroupEndRing.ofHom (A.pullback T.hom) r

theorem groupEndOfFamily_spec (T : Over S) (f : T ⨯ A.scheme ⟶ A.scheme)
    (hf : Group.HomEquations.GroupHomEquations.RespectsGroup A.scheme f) :
    EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T ((groupEndOfFamily A T f hf).hom (A.pullback T.hom)) = f :=
  (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T).apply_symm_apply f

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismEquationBridge.EndomorphismFamilies

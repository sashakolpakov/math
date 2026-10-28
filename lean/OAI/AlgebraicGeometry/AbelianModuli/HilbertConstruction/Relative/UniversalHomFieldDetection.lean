import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalHomFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomLocalRingDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFieldEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso

/-! # Universal Hom Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalHomFieldDetection

noncomputable section

/-! For fixed Noetherian abelian families with a projectively embedded product, field pullbacks detect all homomorphisms on every test scheme. No graph polynomial is supplied. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj
universe u

theorem relativeUniversalAbelianHom_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (T : Over S) (f q : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme)
    [hfMon : IsMonHom f] [hqMon : IsMonHom q]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  apply HilbertConstruction.Over.HomLocalRingDetection.overHom_eq_of_allLocalRingPullbacks
  intro R _ _ s
  let U : Over S := Over.mk (s ≫ T.hom)
  let c : U ⟶ T := Over.homMk s rfl
  let f' := Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f
  let q' := Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c q
  have hf : IsMonHom f := inferInstance
  have hq : IsMonHom q := inferInstance
  have hfm : IsMonHom ((Over.pullback c.left).map f) :=
    (MappedMonoidHomEquations.mappedMonoidHom_iff (Over.pullback c.left) f).mpr
      ⟨congrArg (Over.pullback c.left).map hf.one_hom,
        congrArg (Over.pullback c.left).map hf.mul_hom⟩
  have hqm : IsMonHom ((Over.pullback c.left).map q) :=
    (MappedMonoidHomEquations.mappedMonoidHom_iff (Over.pullback c.left) q).mpr
      ⟨congrArg (Over.pullback c.left).map hq.one_hom,
        congrArg (Over.pullback c.left).map hq.mul_hom⟩
  have hf' : IsMonHom f' := (ParameterPullbackMonoidIso.geometricFamilyMorphismBaseChange_isMonHom_iff c f).mpr hfm
  have hq' : IsMonHom q' := (ParameterPullbackMonoidIso.geometricFamilyMorphismBaseChange_isMonHom_iff c q).mpr hqm
  apply (Geometric.MorphismEquality.geometricFamilyMorphismBaseChange_eq_iff c f q).mp
  exact LocalHomFieldDetection.relativeLocalAbelianHom_eq_of_fieldPullbacks A B j U.hom f' q' (hfMon := hf') (hqMon := hq')
    (Geometric.MorphismFieldEquality.geometricFamilyMorphismBaseChange_fieldEquality c f q h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalHomFieldDetection

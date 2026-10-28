import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPoincareCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.ParameterPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationPositiveTransport

/-! # Parameter Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ParameterRestriction

noncomputable section

/-! Original polarizations restrict to single parameter pullbacks.
The full geometric positivity is preserved and reflected through the
actual two-factor Poincare comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u

private theorem conjugate_comp_right
    {C : Type*} [Category* C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X' ⟶ Y') :
    (eX.hom ≫ f ≫ eY.inv) ≫ eY.hom = eX.hom ≫ f := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem inverse_comp_conjugate
    {C : Type*} [Category* C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X' ⟶ Y') :
    f ≫ eY.inv = eX.inv ≫ (eX.hom ≫ f ≫ eY.inv) := by
  rw [Iso.inv_hom_id_assoc]

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (D : Dual.Data.DualAbelianData A)
  {U T : Over S} (c : U ⟶ T)

theorem parameterMorphism_comparison
    (p : (A.pullback T.hom).scheme ⟶ (D.pullback T.hom).abelian.scheme) :
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p ≫ (D.abelian.parameterPullbackIso c).hom =
      (A.parameterPullbackIso c).hom ≫ (Over.pullback c.left).map p := by
  exact conjugate_comp_right (Single.ParameterBaseChange.singleParameterBaseChangeIso c A.scheme)
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c D.abelian.scheme) ((Over.pullback c.left).map p)

theorem positiveOnGeometricFiber_parameterPullback_iff
    (p : (A.pullback T.hom).scheme ⟶ (D.pullback T.hom).abelian.scheme)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ U.left) :
    PolarizationData.PositiveOnGeometricFiber (D.pullback U.hom) (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p) K s ↔
      PolarizationData.PositiveOnGeometricFiber ((D.pullback T.hom).pullback c.left)
        ((Over.pullback c.left).map p) K s := by
  let eA := A.parameterPullbackIso c
  let eD := D.abelian.parameterPullbackIso c
  let E := (D.pullback T.hom).pullback c.left
  let e : (D.pullback U.hom).abelian.scheme ⊗ (A.pullback U.hom).scheme ≅
      E.abelian.scheme ⊗ ((A.pullback T.hom).pullback c.left).scheme := eD ⊗ᵢ eA
  constructor
  · intro hp
    exact PELModuli.IntegralModel.PolarizationPositiveTransport.positiveOnGeometricFiber_pairComparison (D.pullback U.hom) E
      (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p) ((Over.pullback c.left).map p)
      eA eD (parameterMorphism_comparison A D c p)
      (PELModuli.IntegralModel.InverseLinePullback.inverseLinePullbackIso ((Over.forget U.left).mapIso e)
        (D.pullback U.hom).poincare E.poincare (ParameterPoincareCoherence.parameterPoincareIso A D c)) s hp
  · intro hp
    have he : (Over.pullback c.left).map p ≫ eD.inv =
        eA.inv ≫ Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p :=
      inverse_comp_conjugate eA eD ((Over.pullback c.left).map p)
    exact PELModuli.IntegralModel.PolarizationPositiveTransport.positiveOnGeometricFiber_pairComparison E (D.pullback U.hom)
      ((Over.pullback c.left).map p) (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p)
      eA.symm eD.symm he (ParameterPoincareCoherence.parameterPoincareIso A D c) s hp

def polarizationParameterPullback {δ : Fin g → ℕ}
    (p : PolarizationData.Polarization (D.pullback T.hom) δ) : PolarizationData.Polarization (D.pullback U.hom) δ where
  isogeny := Isogeny.ParameterPullback.isogenyParameterPullback A D.abelian p.isogeny c
  kernelType := (Isogeny.ParameterPullback.isogenyParameterPullback_hasType_iff A D.abelian p.isogeny c δ).mpr
    (p.kernelType.pullback c.left)
  positive K _ _ s := by
    have he : PolarizationData.PositiveOnGeometricFiber (D.pullback U.hom)
        (Isogeny.ParameterPullback.isogenyParameterPullback A D.abelian p.isogeny c).hom K s =
        PolarizationData.PositiveOnGeometricFiber (D.pullback U.hom)
          (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p.isogeny.hom) K s :=
      congrArg (fun f : (A.pullback U.hom).scheme ⟶ (D.pullback U.hom).abelian.scheme =>
        PolarizationData.PositiveOnGeometricFiber (D.pullback U.hom) f K s)
        (Isogeny.ParameterPullback.isogenyParameterPullback_hom A D.abelian p.isogeny c)
    exact Eq.mpr he
      ((positiveOnGeometricFiber_parameterPullback_iff A D c p.isogeny.hom K s).mpr
        ((p.pullback c.left).positive K s))

theorem polarizationParameterPullback_hom {δ : Fin g → ℕ}
    (p : PolarizationData.Polarization (D.pullback T.hom) δ) :
    (polarizationParameterPullback A D c p).isogeny.hom =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p.isogeny.hom :=
  Isogeny.ParameterPullback.isogenyParameterPullback_hom A D.abelian p.isogeny c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ParameterRestriction

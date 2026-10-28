import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ParameterRestriction

/-! # Parameter Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ParameterRecovery

noncomputable section

/-! A polarization on a single parameter pullback gives the identical
polarization on the iterated native pullback through the prescribed
comparisons of the abelian family, dual family, and Poincare line. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u

private theorem transport_square
    {C : Type*} [Category* C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y) :
    f ≫ eY.hom = eX.hom ≫ ((eX.inv ≫ f) ≫ eY.hom) := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem inverse_conjugation
    {C : Type*} [Category* C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X' ⟶ Y') :
    (eX.inv ≫ (eX.hom ≫ f ≫ eY.inv)) ≫ eY.hom = f := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (D : Dual.Data.DualAbelianData A)
  {U T : Over S} (c : U ⟶ T) {δ : Fin g → ℕ}

def polarizationParameterToIterated
    (q : PolarizationData.Polarization (D.pullback U.hom) δ) :
    PolarizationData.Polarization ((D.pullback T.hom).pullback c.left) δ := by
  let eA := A.parameterPullbackIso c
  let eD : (D.pullback U.hom).abelian.scheme ≅
      ((D.pullback T.hom).pullback c.left).abelian.scheme := D.abelian.parameterPullbackIso c
  let : IsMonHom eD.hom := D.abelian.parameterPullbackIso_isMonHom c
  let E := (D.pullback T.hom).pullback c.left
  let k := (q.isogeny.familyTransport eA).targetTransport eD
  let e : (D.pullback U.hom).abelian.scheme ⊗ (A.pullback U.hom).scheme ≅
      E.abelian.scheme ⊗ ((A.pullback T.hom).pullback c.left).scheme := eD ⊗ᵢ eA
  refine ⟨k, (q.kernelType.familyTransport eA).targetTransport eD, ?_⟩
  intro K _ _ s
  have he : q.isogeny.hom ≫ eD.hom = eA.hom ≫ k.hom :=
    transport_square eA eD q.isogeny.hom
  exact PELModuli.IntegralModel.PolarizationPositiveTransport.positiveOnGeometricFiber_pairComparison (D.pullback U.hom) E
    q.isogeny.hom k.hom eA eD he
    (PELModuli.IntegralModel.InverseLinePullback.inverseLinePullbackIso ((Over.forget U.left).mapIso e)
      (D.pullback U.hom).poincare E.poincare (ParameterPoincareCoherence.parameterPoincareIso A D c)) s (q.positive K s)

theorem polarizationParameterToIterated_hom
    (q : PolarizationData.Polarization (D.pullback U.hom) δ) :
    (polarizationParameterToIterated A D c q).isogeny.hom =
      ((A.parameterPullbackIso c).inv ≫ q.isogeny.hom) ≫
        (D.abelian.parameterPullbackIso c).hom := rfl

theorem polarizationParameterToIterated_hom_eq
    (q : PolarizationData.Polarization (D.pullback U.hom) δ)
    (p : (A.pullback T.hom).scheme ⟶ (D.pullback T.hom).abelian.scheme)
    (hq : q.isogeny.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p) :
    (polarizationParameterToIterated A D c q).isogeny.hom = (Over.pullback c.left).map p := by
  rw [polarizationParameterToIterated_hom, hq]
  exact inverse_conjugation (Single.ParameterBaseChange.singleParameterBaseChangeIso c A.scheme)
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c D.abelian.scheme) ((Over.pullback c.left).map p)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ParameterRecovery

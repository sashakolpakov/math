import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkCoordinateLocalization

/-! # Stalk Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.StalkLocalization

noncomputable section

/-! The stalk of the ambient scheme at a point of an affine open is a localization of that open's coordinate ring. The actual affine coordinate map to the open composes to the ambient stalk morphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {T X : Scheme.{u}} [IsAffine T] (t : T ⟶ X) [IsOpenImmersion t] (x : T)

local instance : (T.isoSpec.hom x).asIdeal.IsPrime :=
  (show PrimeSpectrum Γ(T, ⊤) from T.isoSpec.hom x).isPrime

@[instance_reducible]
def affineOpenTargetStalkAlgebra : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) :=
  ((asIso (t.stalkMap x)).inv.hom.comp (T.presheaf.germ ⊤ x trivial).hom).toAlgebra

def affineOpenStalkAlgEquiv :
    let : Algebra Γ(T, ⊤) (T.presheaf.stalk x) := Affine.StalkCoordinateLocalization.affineStalkCoordinateAlgebra T x;
    let : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) := affineOpenTargetStalkAlgebra t x;
    T.presheaf.stalk x ≃ₐ[Γ(T, ⊤)] X.presheaf.stalk (t x) := by
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk x) := Affine.StalkCoordinateLocalization.affineStalkCoordinateAlgebra T x
  letI : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) := affineOpenTargetStalkAlgebra t x
  exact { (asIso (t.stalkMap x)).symm.commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }

theorem affineOpenTargetStalk_isLocalization :
    let : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) := affineOpenTargetStalkAlgebra t x;
    IsLocalization (T.isoSpec.hom x).asIdeal.primeCompl (X.presheaf.stalk (t x)) := by
  let : Algebra Γ(T, ⊤) (T.presheaf.stalk x) := Affine.StalkCoordinateLocalization.affineStalkCoordinateAlgebra T x
  let : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) := affineOpenTargetStalkAlgebra t x
  let : IsLocalization (T.isoSpec.hom x).asIdeal.primeCompl (T.presheaf.stalk x) :=
    Affine.StalkCoordinateLocalization.affineStalkCoordinate_isLocalization T x
  exact IsLocalization.isLocalization_of_algEquiv (T.isoSpec.hom x).asIdeal.primeCompl
    (affineOpenStalkAlgEquiv t x)

def affineOpenTargetStalkLocalizationEquiv :
    let : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) := affineOpenTargetStalkAlgebra t x;
    Localization.AtPrime (T.isoSpec.hom x).asIdeal ≃ₐ[Γ(T, ⊤)] X.presheaf.stalk (t x) := by
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk x) := Affine.StalkCoordinateLocalization.affineStalkCoordinateAlgebra T x
  letI : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) := affineOpenTargetStalkAlgebra t x
  exact (Affine.StalkCoordinateLocalization.affineStalkCoordinateLocalizationEquiv T x).trans (affineOpenStalkAlgEquiv t x)

theorem affineOpenTargetStalk_coordinateMap_comp :
    let : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) := affineOpenTargetStalkAlgebra t x;
    Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(T, ⊤) (X.presheaf.stalk (t x))) ≫ t = X.fromSpecStalk (t x) := by
  let : Algebra Γ(T, ⊤) (X.presheaf.stalk (t x)) := affineOpenTargetStalkAlgebra t x
  let e := asIso (t.stalkMap x)
  have hc : Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(T, ⊤) (X.presheaf.stalk (t x))) =
      Spec.map e.inv ≫ Affine.QuotientCoefficientMap.affineCoordinateMap (T.presheaf.germ ⊤ x trivial).hom := by
    change Spec.map (T.presheaf.germ ⊤ x trivial ≫ e.inv) ≫ T.isoSpec.inv =
      Spec.map e.inv ≫ (Spec.map (T.presheaf.germ ⊤ x trivial) ≫ T.isoSpec.inv)
    rw [Spec.map_comp, Category.assoc]
  dsimp only
  rw [hc, Affine.StalkCoordinateLocalization.affineCoordinateMap_germ_eq_fromSpecStalk T x, Category.assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk t, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (e.hom ≫ e.inv) ≫ X.fromSpecStalk (t x) = X.fromSpecStalk (t x)
  rw [e.hom_inv_id, Spec.map_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.StalkLocalization

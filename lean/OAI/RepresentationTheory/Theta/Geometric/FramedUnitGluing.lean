import OAI.RepresentationTheory.Theta.Geometric.FramedUnitRestriction

/-! # Framed Unit Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.FramedUnitGluing

noncomputable section

/-! A compatible family of regular gauges gives a global isomorphism of
the actual algebraic line-bundle sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_iso_of_framed_units {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.over (U i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (g : ∀ i, N.over (U i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (r : ∀ i, Γ(X, U i)ˣ)
    (a b : ∀ i k, Γ(X, U i ⊓ U k))
    (he : ∀ i k,
      (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (U i) (e i)
        (Over.mk (homOfLE (show U i ⊓ U k ≤ U i from inf_le_left)))).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (U k) (e k)
        (Over.mk (homOfLE (show U i ⊓ U k ≤ U k from inf_le_right)))).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf (U i ⊓ U k) (a i k))
    (hg : ∀ i k,
      (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N (U i) (g i)
        (Over.mk (homOfLE (show U i ⊓ U k ≤ U i from inf_le_left)))).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N (U k) (g k)
        (Over.mk (homOfLE (show U i ⊓ U k ≤ U k from inf_le_right)))).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf (U i ⊓ U k) (b i k))
    (hr : ∀ i k,
      a i k * (PowerGaugeCover.restrictRegularUnit (show U i ⊓ U k ≤ U i from inf_le_left) (r i) : Γ(X, U i ⊓ U k)) =
      (PowerGaugeCover.restrictRegularUnit (show U i ⊓ U k ≤ U k from inf_le_right) (r k) : Γ(X, U i ⊓ U k)) * b i k) :
    ∃ f : M ≅ N, ∀ i, f.hom.over (U i) = (FramedUnitIsomorphisms.framedUnitIso M N (U i) (e i) (g i) (r i)).hom := by
  apply LineBundleIsoGluing.exists_moduleIso_of_localIsos M N U hU (fun i => FramedUnitIsomorphisms.framedUnitIso M N (U i) (e i) (g i) (r i))
  intro i k
  have hl := congrArg Iso.hom (FramedUnitRestriction.framedUnitIso_restrict M N
    (show U i ⊓ U k ≤ U i from inf_le_left) (e i) (g i) (r i))
  have hk := congrArg Iso.hom (FramedUnitRestriction.framedUnitIso_restrict M N
    (show U i ⊓ U k ≤ U k from inf_le_right) (e k) (g k) (r k))
  exact hl.trans ((FramedUnitIsomorphisms.framedUnitIso_eq_of_transitions M N (U i ⊓ U k)
    _ _ _ _ (a i k) (b i k) _ _ (he i k) (hg i k) (hr i k)).trans hk.symm)

theorem consecutivePowerGauge_identity {A : Type*} [CommGroup A] (n : ℕ) (f g r s : A)
    (h : s * f ^ (n + 1) = r * g ^ n) : (g / f) ^ n * r = s * f := by
  calc
    (g / f) ^ n * r = (r * g ^ n) / f ^ n := by
      rw [div_pow, div_mul_eq_mul_div, mul_comm (g ^ n) r]
    _ = (s * f ^ (n + 1)) / f ^ n := by rw [h]
    _ = s * f := by
      rw [pow_succ]
      calc
        (s * (f ^ n * f)) / f ^ n = ((s * f) * f ^ n) / f ^ n := by ac_rfl
        _ = s * f := mul_div_cancel_right _ _

end

end OAI.RepresentationTheory.Theta.Geometric.FramedUnitGluing

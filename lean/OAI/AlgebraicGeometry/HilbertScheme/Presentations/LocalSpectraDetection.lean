import Mathlib.AlgebraicGeometry.Stalk

/-! # Local Spectra Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalSpectraDetection

noncomputable section

/-! Maps of schemes are detected on their actual local spectra, without
any noetherianity hypothesis on the source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem localSpectrumPoint_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    SpecToEquivOfLocalRing Y (X.presheaf.stalk x) (X.fromSpecStalk x ≫ f) =
      ⟨f x, f.stalkMap x, inferInstance⟩ := by
  apply SpecToEquivOfLocalRing_eq_iff.mpr
  refine ⟨?_, ?_⟩
  · exact congrArg f Scheme.fromSpecStalk_closedPoint
  · change Scheme.stalkClosedPointTo (X.fromSpecStalk x ≫ f) = _
    rw [Scheme.stalkClosedPointTo_comp, Scheme.stalkClosedPointTo_fromSpecStalk]
    exact Scheme.Hom.stalkMap_congr_point f _ _ Scheme.fromSpecStalk_closedPoint

theorem schemeHom_eq_of_localSpectra {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (h : ∀ x : X, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  have hp (x : X) :
      (⟨f x, f.stalkMap x, inferInstance⟩ :
        Σ y, {a : Y.presheaf.stalk y ⟶ X.presheaf.stalk x // IsLocalHom a.hom}) =
          ⟨g x, g.stalkMap x, inferInstance⟩ := by
    have he := congrArg (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)) (h x)
    rw [localSpectrumPoint_comp, localSpectrumPoint_comp] at he
    exact he
  have hb : f.base = g.base := by
    ext x
    exact congrArg Sigma.fst (hp x)
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  have he := SheafedSpace.hom_stalk_ext f.toLRSHom.toShHom g.toLRSHom.toShHom hb
    (fun x => (SpecToEquivOfLocalRing_eq_iff.mp (hp x)).choose_spec)
  exact congrArg (fun a => a.hom) he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalSpectraDetection

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.MapSmoothFiberCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberCartesianComparison

/-! # Scheme Smooth Fiber Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeSmoothFiberCriterion

noncomputable section

/-! The pointwise smooth-fiber criterion holds for arbitrary affine source and target schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineScheme_stalk_formallySmooth_of_smooth_fiber
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] (x : X) [Smooth (f.fiberToSpecResidueField (f x))] :
    (f.stalkMap x).hom.FormallySmooth := by
  let g : Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤) := X.isoSpec.inv ≫ f ≫ S.isoSpec.hom
  have : Flat g := inferInstance
  have : LocallyOfFinitePresentation g := inferInstance
  have H : IsPullback X.isoSpec.hom f g S.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨by
      dsimp only [g]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]⟩
  have hfib : Smooth (g.fiberToSpecResidueField (S.isoSpec.hom (f x))) :=
    (HilbertConstruction.Smooth.FiberCartesianComparison.smooth_fiber_iff_of_isPullback _ f g _ H (f x)).mp inferInstance
  have he : g (X.isoSpec.hom x) = S.isoSpec.hom (f x) := by
    simp [g]
  have hlocal : (g.stalkMap (X.isoSpec.hom x)).hom.FormallySmooth := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective g
    have : Flat (Spec.map φ) := hφ.symm ▸ (inferInstanceAs (Flat g))
    have : LocallyOfFinitePresentation (Spec.map φ) := hφ.symm ▸ (inferInstanceAs (LocallyOfFinitePresentation g))
    have : Smooth ((Spec.map φ).fiberToSpecResidueField (Spec.map φ (X.isoSpec.hom x))) := by
      rw [hφ, he]
      exact hfib
    exact (congrArg (fun a : Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤) =>
      (a.stalkMap (X.isoSpec.hom x)).hom.FormallySmooth) hφ).mp
        (HilbertConstruction.Spec.MapSmoothFiberCriterion.specMap_stalk_formallySmooth_of_smooth_fiber φ (X.isoSpec.hom x))
  change ((X.isoSpec.inv ≫ f ≫ S.isoSpec.hom).stalkMap (X.isoSpec.hom x)).hom.FormallySmooth at hlocal
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hlocal
  let x' := X.isoSpec.inv (X.isoSpec.hom x)
  let A₀ := (Spec Γ(S, ⊤)).presheaf.stalk (S.isoSpec.hom (f x'))
  let A₁ := S.presheaf.stalk (f x')
  let A₂ := X.presheaf.stalk x'
  let A₃ := (Spec Γ(X, ⊤)).presheaf.stalk (X.isoSpec.hom x)
  let a : A₀ ⟶ A₁ := S.isoSpec.hom.stalkMap (f x')
  let b : A₁ ⟶ A₂ := f.stalkMap x'
  let c : A₂ ⟶ A₃ := X.isoSpec.inv.stalkMap (X.isoSpec.hom x)
  have : IsIso a := inferInstanceAs (IsIso (S.isoSpec.hom.stalkMap (f x')))
  have : IsIso c := inferInstanceAs (IsIso (X.isoSpec.inv.stalkMap (X.isoSpec.hom x)))
  change ((a ≫ b) ≫ c).hom.FormallySmooth at hlocal
  rw [CommRingCat.hom_comp,
    RingHom.FormallySmooth.respectsIso.cancel_right_isIso, CommRingCat.hom_comp,
    RingHom.FormallySmooth.respectsIso.cancel_left_isIso] at hlocal
  have hx : X.isoSpec.inv (X.isoSpec.hom x) = x := by simp
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (f.arrowStalkMapIsoOfEq hx)).mp hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeSmoothFiberCriterion

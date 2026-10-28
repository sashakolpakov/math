import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction

/-! # Frame Scalar Transport -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameScalarTransport

noncomputable section

/-! A scalar transition on an open subscheme gives the same transition on the
equivalent over-site, with the original section of the ambient structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction

private theorem frameUnitCancel {C : Type*} [Category C] {A B P Q : C}
    (a : A ⟶ B) (b : B ⟶ Q) (i : P ≅ Q) :
    (a ≫ b ≫ i.inv) ≫ i.hom = a ≫ b := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem faithfulFrameScalarTransport {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) [G.Faithful] {P Q : C} {B : D} (i : G.obj Q ≅ B)
    (e g : P ⟶ Q) (s : Q ⟶ Q) (t : B ⟶ B)
    (h : G.map e ≫ i.hom = (G.map g ≫ i.hom) ≫ t)
    (hs : G.map s ≫ i.hom = i.hom ≫ t) : e = g ≫ s := by
  apply G.map_injective
  apply (cancel_mono i.hom).mp
  rw [Functor.map_comp, Category.assoc, hs]
  exact h.trans (Category.assoc _ _ _)

theorem algebraicOverFrame_scalar {X : Scheme.{0}} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (r : Γ(X, U))
    (h : e.hom = g.hom ≫ SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (SheafCohomology.Projective.OpenFrames.Scheme.Modules.openTopSection U r)) :
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom =
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U g).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
  let G := (Scheme.Modules.overEquiv U).functor
  let I := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  have he (f : M.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
      G.map (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U f).hom ≫ I.hom =
        ((Scheme.Modules.overFunctorEquiv U).app M).hom ≫ f.hom := by
    simp only [G, I, SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso,
      Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
    change (((Scheme.Modules.overFunctorEquiv U).app M).hom ≫ f.hom ≫ I.inv) ≫ I.hom = _
    exact frameUnitCancel _ _ I
  apply faithfulFrameScalarTransport G I _ _ _
    (SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (SheafCohomology.Projective.OpenFrames.Scheme.Modules.openTopSection U r))
  · exact (he e).trans ((congrArg (fun q => ((Scheme.Modules.overFunctorEquiv U).app M).hom ≫ q) h).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (SheafCohomology.Projective.OpenFrames.Scheme.Modules.openTopSection U r)) (he g).symm)))
  · exact SheafCohomology.Projective.OverScalarRestriction.overEquiv_unitScalarEnd U r

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameScalarTransport

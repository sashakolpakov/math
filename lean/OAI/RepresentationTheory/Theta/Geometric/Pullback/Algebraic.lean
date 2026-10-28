import OAI.RepresentationTheory.Theta.Geometric.AlgebraicQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions

/-! # Algebraic -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.Algebraic

noncomputable section

section

/-! Exact transitions of the actual algebraic twists, in their native frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def algebraicTwistRestrictionFrame (n : ℕ) (d : ℤ) (i : Fin (n + 1)) :
    (AlgebraicQuotient.algebraicTwistBundle n d).sheaf.restrict (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i).ι ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i).toScheme :=
  AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization i 0 d

theorem algebraicTwistRestrictionFrame_transition (n : ℕ) (d : ℤ) (i k : Fin (n + 1)) :
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)
      (algebraicTwistRestrictionFrame n d i)).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k)
      (algebraicTwistRestrictionFrame n d k)).hom ≫
        AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
          ((AlgebraicGeometry.SheafCohomology.Projective.OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := ℂ) i k ^ d :
            Γ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)ˣ) :
            Γ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)) :=
  AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions.MvPolynomial.coordinateHyperplaneTwistTrivialization_restrict_transition i k 0 d

end

section

/-! Pullback carries multiplication by an actual regular function to
multiplication by its pullback, under the canonical structure-sheaf frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullback_unitEndomorphism {X Y : Scheme} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) ≫
        (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (f.appTop r) := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  have hu : adj.homEquiv _ _ (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hu]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Γ(Y, U.unop) at a
  change f.app U.unop (a * Y.presheaf.map U.unop.leTop.op r) =
    f.app U.unop a * X.presheaf.map (f ⁻¹ᵁ U.unop).leTop.op (f.appTop r)
  rw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom (f.naturality U.unop.leTop.op) r

end

/-! Pull back actual open-scheme frames and their scalar transition maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def pullbackOpenFrame {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ U).toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app ((Scheme.Modules.pullback f).obj M) ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm.app M ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e) ≪≫
    AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso (f ∣_ U)

theorem pullbackOpenFrame_scalar {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (r : Γ(U.toScheme, ⊤))
    (h : e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) :
    (pullbackOpenFrame f M U e).hom =
      (pullbackOpenFrame f M U g).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((f ∣_ U).appTop r) := by
  simp only [pullbackOpenFrame, Iso.trans_hom, Functor.mapIso_hom, h,
    Functor.map_comp, Category.assoc]
  rw [pullback_unitEndomorphism]

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.Algebraic

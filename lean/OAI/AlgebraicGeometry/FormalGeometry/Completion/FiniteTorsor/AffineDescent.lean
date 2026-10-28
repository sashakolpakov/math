import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteValues
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.DescentFiniteEtale

/-! # Affine Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: descended algebras of the actual finite torsors on affine bases

A local lift over a faithfully flat weakly étale affine cover supplies the
actual local representative. Its canonical coaction descends to an algebra
over the original ring, with a checked isomorphism after base change.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))
  (ℓ n : ℕ) [NeZero (ℓ ^ n)]

/-- The actual affine coordinate algebra represents the local finite coefficient scheme in the slice. -/
def AffineDescent.Construction.finiteCoefficientSliceAlgebraIso :
    (Affine.CoverObject.Construction.affineAlgebraToSlice f hf).obj (op (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S)) ≅
      Local.Construction.finiteCoefficientSlice ℓ n (Affine.CoverObject.Construction.affineCoverObject f hf) :=
  (ProEtale.Slice.Construction.proEtaleToSlice (Affine.CoverObject.Construction.affineCoverObject f hf)).mapIso (ProEtale.Slice.Construction.finiteCoefficientAlgebraSpecIso ℓ n S) ≪≫
    eqToIso (ProEtale.Slice.Construction.proEtaleToSlice_finiteCoefficient (Affine.CoverObject.Construction.affineCoverObject f hf) ℓ n)

variable {ℓ n} (E : App.Construction.FiniteCoefficientExtension ℓ n (Spec (CommRingCat.of R)))
  (s : E.Fiber (Affine.CoverObject.Construction.affineCoverObject f hf))

/-- The actual torsor restricted to affine objects over the cover is represented by its coefficient algebra. -/
def App.Construction.FiniteCoefficientExtension.affineLocalRepresentative :
    ((Affine.CoverObject.Construction.affineAlgebraToSlice f hf).op ⋙ (Over.forget (Affine.CoverObject.Construction.affineCoverObject f hf)).op ⋙
      E.fiberPresheaf).RepresentableBy (op (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S)) := by
  let rep := (E.localRepresentative s).ofIsoObj (AffineDescent.Construction.finiteCoefficientSliceAlgebraIso f hf ℓ n)
  exact {
    homEquiv := (Affine.CoverObject.Construction.affineAlgebraToSliceFullyFaithful f hf).homEquiv.trans rep.homEquiv
    homEquiv_comp g h := by
      change rep.homEquiv ((Affine.CoverObject.Construction.affineAlgebraToSlice f hf).map (g ≫ h)) = _
      rw [CategoryTheory.Functor.map_comp, rep.homEquiv_comp]
      rfl }

/-- On algebras, the same actual local representative is a corepresentative. -/
def App.Construction.FiniteCoefficientExtension.affineLocalCorepresentative :
    (Affine.SiteValues.Construction.affineSliceValues f hf E.fiberPresheaf).CorepresentableBy (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S) where
  homEquiv := {
    toFun g := (E.affineLocalRepresentative f hf s).homEquiv g.op
    invFun t := ((E.affineLocalRepresentative f hf s).homEquiv.symm t).unop
    left_inv g := congrArg Quiver.Hom.unop
      ((E.affineLocalRepresentative f hf s).homEquiv.symm_apply_apply g.op)
    right_inv t := (E.affineLocalRepresentative f hf s).homEquiv.apply_symm_apply t }
  homEquiv_comp g h := by
    simpa only [op_comp] using! (E.affineLocalRepresentative f hf s).homEquiv_comp g.op h.op

/-- The corepresentative is for the actual original torsor values after scalar restriction. -/
def App.Construction.FiniteCoefficientExtension.affineRestrictedCorepresentative :
    (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf ⋙ Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf).CorepresentableBy
      (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S) :=
  (E.affineLocalCorepresentative f hf s).ofIso (Affine.SiteValues.Construction.affineSliceValuesIso f hf E.fiberPresheaf)

variable (hflat : f.FaithfullyFlat)

/-- The actual finite torsor's descended algebra over the original affine base. -/
def App.Construction.FiniteCoefficientExtension.affineDescendedAlgebra : CommAlgCat.{u} R :=
  Affine.DescentData.Construction.affineRepresentativeDescended f hf (Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf)
    (E.affineRestrictedCorepresentative f hf s) hflat

/-- Base change recovers the actual coordinate algebra of the torsor's local finite étale representative. -/
def App.Construction.FiniteCoefficientExtension.affineDescendedAlgebraIso :
    (CommBaseChange.Construction.commAlgExtend f).obj (E.affineDescendedAlgebra f hf s hflat) ≅
      (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S).obj :=
  Affine.DescentData.Construction.affineRepresentativeDescendedIso f hf (Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf)
    (E.affineRestrictedCorepresentative f hf s) hflat

theorem App.Construction.FiniteCoefficientExtension.affineDescendedAlgebra_finite : Module.Finite R (E.affineDescendedAlgebra f hf s hflat) :=
  Affine.DescentFiniteEtale.Construction.affineRepresentativeDescended_finite f hf ℓ n (Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf)
    (E.affineRestrictedCorepresentative f hf s) hflat

theorem App.Construction.FiniteCoefficientExtension.affineDescendedAlgebra_etale : Algebra.Etale R (E.affineDescendedAlgebra f hf s hflat) :=
  Affine.DescentFiniteEtale.Construction.affineRepresentativeDescended_etale f hf ℓ n (Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf)
    (E.affineRestrictedCorepresentative f hf s) hflat

/-- The spectrum of the actual descended algebra, as an object of the original pro-étale site. -/
def App.Construction.FiniteCoefficientExtension.affineDescendedProEt : (Spec (CommRingCat.of R)).ProEt := by
  have h : Algebra.Etale R (E.affineDescendedAlgebra f hf s hflat) :=
    E.affineDescendedAlgebra_etale f hf s hflat
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (E.affineDescendedAlgebra f hf s hflat)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr ((RingHom.etale_algebraMap).mpr h)
  exact Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap R (E.affineDescendedAlgebra f hf s hflat))))

theorem App.Construction.FiniteCoefficientExtension.affineDescendedProEt_finite : IsFinite (E.affineDescendedProEt f hf s hflat).hom :=
  (IsFinite.SpecMap_iff _).mpr
    ((RingHom.finite_algebraMap).mpr (E.affineDescendedAlgebra_finite f hf s hflat))

theorem App.Construction.FiniteCoefficientExtension.affineDescendedProEt_etale : Etale (E.affineDescendedProEt f hf s hflat).hom :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    ((RingHom.etale_algebraMap).mpr (E.affineDescendedAlgebra_etale f hf s hflat))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

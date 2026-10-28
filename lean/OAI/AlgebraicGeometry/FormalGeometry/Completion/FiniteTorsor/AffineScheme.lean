import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.AffineRepresentation
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteDensity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.DenseRepresentation

/-! # Affine Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: actual finite étale torsor schemes on affine bases

An affine faithfully flat trivialization gives a finite étale scheme
representing the original torsor on the whole pro-étale site. The identification
on arbitrary objects follows from the proved affine cover density.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))
  {ℓ n : ℕ} [NeZero (ℓ ^ n)]

variable (E : App.Construction.FiniteCoefficientExtension ℓ n (Spec (CommRingCat.of R)))
  (s : E.Fiber (Affine.CoverObject.Construction.affineCoverObject f hf)) (hflat : f.FaithfullyFlat)

/-- The actual representing bijection on spectra, expressed as a presheaf representation. -/
def App.Construction.FiniteCoefficientExtension.affineDescendedRestrictedRepresentative :
    ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).op ⋙ E.fiberPresheaf).RepresentableBy
      (op (E.affineDescendedSiteAlgebra f hf s hflat)) where
  homEquiv := {
    toFun g := (E.affineDescendedCorepresentative f hf s hflat).homEquiv g.unop
    invFun t := ((E.affineDescendedCorepresentative f hf s hflat).homEquiv.symm t).op
    left_inv g := congrArg Quiver.Hom.op
      ((E.affineDescendedCorepresentative f hf s hflat).homEquiv.symm_apply_apply g.unop)
    right_inv t := (E.affineDescendedCorepresentative f hf s hflat).homEquiv.apply_symm_apply t }
  homEquiv_comp g h := by
    simpa only [unop_comp] using!
      (E.affineDescendedCorepresentative f hf s hflat).homEquiv_comp g.unop h.unop

/-- The actual descended finite étale scheme represents the original torsor on the whole site. -/
def App.Construction.FiniteCoefficientExtension.affineDescendedRepresentative :
    E.fiberPresheaf.RepresentableBy (E.affineDescendedProEt f hf s hflat) := by
  have := Affine.SiteDensity.Construction.proEtaleAlgebraSpecCoverDense R
  exact DenseRepresentation.Construction.representableByOfCoverDense.{u + 1, u, u + 1, u, u + 1}
    (ProEtale.Algebras.Construction.proEtaleAlgebraSpec R) (ProEtale.Algebras.Construction.proEtaleAlgebraSpecFullyFaithful (R := R))
    (Scheme.ProEt.topology (Spec (CommRingCat.of R))) E.fiberSheaf
    (E.affineDescendedRestrictedRepresentative f hf s hflat)

include s hflat in
/-- An actual finite étale representative exists whenever an affine faithfully flat trivialization is given. -/
theorem App.Construction.FiniteCoefficientExtension.exists_finiteEtale_representative_of_affine_trivialization :
    ∃ T : (Spec (CommRingCat.of R)).ProEt,
      IsFinite T.hom ∧ Etale T.hom ∧ Nonempty (E.fiberPresheaf.RepresentableBy T) :=
  ⟨E.affineDescendedProEt f hf s hflat, E.affineDescendedProEt_finite f hf s hflat,
    E.affineDescendedProEt_etale f hf s hflat, ⟨E.affineDescendedRepresentative f hf s hflat⟩⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

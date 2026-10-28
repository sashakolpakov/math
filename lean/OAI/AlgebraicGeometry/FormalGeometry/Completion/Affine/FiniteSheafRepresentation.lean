import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.AffineScheme

/-! # Finite Sheaf Representation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.FiniteSheafRepresentation.Construction

noncomputable section

/-!
# Completion: affine descent for an actual sheaf with a finite constant local representative

This version of the proved descent construction accepts the local representing
isomorphism directly, so it also applies to torsors restricted from a larger base.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))
  (ℓ n : ℕ) [NeZero (ℓ ^ n)]
  (F : Sheaf (Scheme.ProEt.topology (Spec (CommRingCat.of R))) (Type (max w u)))
  (rep : ((Over.forget (CoverObject.Construction.affineCoverObject f hf)).op ⋙ F.obj).RepresentableBy
    (FiniteTorsor.Local.Construction.finiteCoefficientSlice ℓ n (CoverObject.Construction.affineCoverObject f hf)))

/-- The supplied local representing isomorphism on the affine objects over the cover. -/
def affineSheafLocalRepresentative :
    ((CoverObject.Construction.affineAlgebraToSlice f hf).op ⋙ (Over.forget (CoverObject.Construction.affineCoverObject f hf)).op ⋙ F.obj).RepresentableBy
      (op (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S)) := by
  let rep' := rep.ofIsoObj (FiniteTorsor.AffineDescent.Construction.finiteCoefficientSliceAlgebraIso f hf ℓ n)
  exact {
    homEquiv := (CoverObject.Construction.affineAlgebraToSliceFullyFaithful f hf).homEquiv.trans rep'.homEquiv
    homEquiv_comp g h := by
      change rep'.homEquiv ((CoverObject.Construction.affineAlgebraToSlice f hf).map (g ≫ h)) = _
      rw [CategoryTheory.Functor.map_comp, rep'.homEquiv_comp]
      rfl }

/-- The actual local sheaf values are corepresented by the finite coefficient algebra. -/
def affineSheafLocalCorepresentative :
    (SiteValues.Construction.affineSliceValues f hf F.obj).CorepresentableBy (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S) where
  homEquiv := {
    toFun g := (affineSheafLocalRepresentative f hf ℓ n F rep).homEquiv g.op
    invFun t := ((affineSheafLocalRepresentative f hf ℓ n F rep).homEquiv.symm t).unop
    left_inv g := congrArg Quiver.Hom.unop
      ((affineSheafLocalRepresentative f hf ℓ n F rep).homEquiv.symm_apply_apply g.op)
    right_inv t := (affineSheafLocalRepresentative f hf ℓ n F rep).homEquiv.apply_symm_apply t }
  homEquiv_comp g h := by
    simpa only [op_comp] using!
      (affineSheafLocalRepresentative f hf ℓ n F rep).homEquiv_comp g.op h.op

/-- The local corepresentative for scalar restriction of the actual affine values. -/
def affineSheafRestrictedCorepresentative :
    (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf ⋙ SiteValues.Construction.proEtaleAffineValues F.obj).CorepresentableBy
      (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S) :=
  (affineSheafLocalCorepresentative f hf ℓ n F rep).ofIso (SiteValues.Construction.affineSliceValuesIso f hf F.obj)

variable (hflat : f.FaithfullyFlat)

/-- The actual descended algebra of the locally represented sheaf. -/
def affineSheafDescendedAlgebra : CommAlgCat.{u} R :=
  DescentData.Construction.affineRepresentativeDescended f hf (SiteValues.Construction.proEtaleAffineValues F.obj)
    (affineSheafRestrictedCorepresentative f hf ℓ n F rep) hflat

theorem affineSheafDescendedAlgebra_finite :
    Module.Finite R (affineSheafDescendedAlgebra f hf ℓ n F rep hflat) :=
  DescentFiniteEtale.Construction.affineRepresentativeDescended_finite f hf ℓ n (SiteValues.Construction.proEtaleAffineValues F.obj)
    (affineSheafRestrictedCorepresentative f hf ℓ n F rep) hflat

theorem affineSheafDescendedAlgebra_etale :
    Algebra.Etale R (affineSheafDescendedAlgebra f hf ℓ n F rep hflat) :=
  DescentFiniteEtale.Construction.affineRepresentativeDescended_etale f hf ℓ n (SiteValues.Construction.proEtaleAffineValues F.obj)
    (affineSheafRestrictedCorepresentative f hf ℓ n F rep) hflat

/-- The descended algebra is an object of the actual affine site. -/
def affineSheafDescendedSiteAlgebra : ProEtale.Algebras.Construction.ProEtaleAlgebra R := by
  have h : Algebra.Etale R (affineSheafDescendedAlgebra f hf ℓ n F rep hflat) :=
    affineSheafDescendedAlgebra_etale f hf ℓ n F rep hflat
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R
      (affineSheafDescendedAlgebra f hf ℓ n F rep hflat)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr h)
  exact ⟨affineSheafDescendedAlgebra f hf ℓ n F rep hflat, by
    change WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R
      (affineSheafDescendedAlgebra f hf ℓ n F rep hflat))))
    infer_instance⟩

/-- Actual sections and actual algebra descent identify the affine corepresentative. -/
def affineSheafDescendedCorepresentative :
    (SiteValues.Construction.proEtaleAffineValues F.obj).CorepresentableBy (affineSheafDescendedSiteAlgebra f hf ℓ n F rep hflat) :=
  CorepresentableEffectiveDescent.Construction.descendedCorepresentative (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf) (SiteValues.Construction.proEtaleAffineValues F.obj)
    (affineSheafRestrictedCorepresentative f hf ℓ n F rep)
    (ProEtale.DescentComparison.Construction.proEtaleComparisonFullyFaithful f hf hflat)
    (SheafDescent.Construction.proEtaleAffineSectionToDescent_bijective f hf hflat F)
    (ProEtale.DescentComparison.Construction.proEtaleComparisonIso f hf (CommDescentObject.Construction.descendedCommAlgebraCounit f hflat
      (DescentData.Construction.affineRepresentativeCoalgebra f hf (SiteValues.Construction.proEtaleAffineValues F.obj)
        (affineSheafRestrictedCorepresentative f hf ℓ n F rep))))

/-- The same representing bijection on the spectrum subcategory. -/
def affineSheafDescendedRestrictedRepresentative :
    ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).op ⋙ F.obj).RepresentableBy
      (op (affineSheafDescendedSiteAlgebra f hf ℓ n F rep hflat)) where
  homEquiv := {
    toFun g := (affineSheafDescendedCorepresentative f hf ℓ n F rep hflat).homEquiv g.unop
    invFun t := ((affineSheafDescendedCorepresentative f hf ℓ n F rep hflat).homEquiv.symm t).op
    left_inv g := congrArg Quiver.Hom.op
      ((affineSheafDescendedCorepresentative f hf ℓ n F rep hflat).homEquiv.symm_apply_apply g.unop)
    right_inv t := (affineSheafDescendedCorepresentative f hf ℓ n F rep hflat).homEquiv.apply_symm_apply t }
  homEquiv_comp g h := by
    simpa only [unop_comp] using!
      (affineSheafDescendedCorepresentative f hf ℓ n F rep hflat).homEquiv_comp g.unop h.unop

/-- The actual sheaf is represented on the whole site by the descended spectrum. -/
def affineSheafDescendedRepresentative :
    F.obj.RepresentableBy ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).obj
      (op (affineSheafDescendedSiteAlgebra f hf ℓ n F rep hflat))) := by
  have := SiteDensity.Construction.proEtaleAlgebraSpecCoverDense R
  exact DenseRepresentation.Construction.representableByOfCoverDense.{u + 1, u, u + 1, u, w}
    (ProEtale.Algebras.Construction.proEtaleAlgebraSpec R) (ProEtale.Algebras.Construction.proEtaleAlgebraSpecFullyFaithful (R := R))
    (Scheme.ProEt.topology (Spec (CommRingCat.of R))) F
    (affineSheafDescendedRestrictedRepresentative f hf ℓ n F rep hflat)

include rep hflat in
/-- A finite constant local representative descends to a finite étale representative. -/
theorem exists_affineSheaf_finiteEtale_representative :
    ∃ T : (Spec (CommRingCat.of R)).ProEt,
      IsFinite T.hom ∧ Etale T.hom ∧ Nonempty (F.obj.RepresentableBy T) := by
  refine ⟨(ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).obj (op (affineSheafDescendedSiteAlgebra f hf ℓ n F rep hflat)),
    ?_, ?_, ⟨affineSheafDescendedRepresentative f hf ℓ n F rep hflat⟩⟩
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr
      (affineSheafDescendedAlgebra_finite f hf ℓ n F rep hflat))
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr
      (affineSheafDescendedAlgebra_etale f hf ℓ n F rep hflat))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.FiniteSheafRepresentation.Construction

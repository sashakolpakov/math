import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGroupoidIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Quotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Limits

/-! # Affine Quotient Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineQuotientOf.Construction.AffineQuotient

/-!
# Quotients of closed finite-free affine equivalence relations

The quotient is the spectrum of the invariant ring. Its projection is finite
locally free and surjective, its kernel pair is the original relation, and
it has the quotient universal property against all scheme targets.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- The quotient projection, with the original affine scheme as its domain. -/
noncomputable abbrev projection {U V : Scheme.{u}} [IsAffine U] (s t : V ⟶ U) :
    U ⟶ AffineRing.Construction.Affine.quotient s.appTop.hom t.appTop.hom :=
  U.isoSpec.hom ≫ AffineRing.Construction.Affine.projection s.appTop.hom t.appTop.hom

/-- The actual affine quotient projection is finite locally free and surjective,
and the given relation is its kernel pair. -/
theorem projection_properties
    {U V S : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine S]
    (a : U ⟶ S) (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    (h : s ≫ a = t ≫ a) [IsClosedImmersion (pullback.lift s t h)]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := s.appTop.hom.toAlgebra; Module.Basis ι Γ(U, ⊤) Γ(V, ⊤)) :
    IsFinite (projection s t) ∧ Flat (projection s t) ∧
      LocallyOfFinitePresentation (projection s t) ∧ Surjective (projection s t) ∧
      IsKernelPair (projection s t) s t := by
  obtain ⟨hfin, hflat, hfp, hsurj⟩ :=
    AffineGroupoidIs.Construction.AffineGroupoid.quotient_projection_finiteLocallyFree_surjective a s t e h b
  let := hfin
  let := hflat
  let := hfp
  let := hsurj
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hk := AffineGroupoidIs.Construction.AffineGroupoid.quotient_projection_isKernelPair a s t e h b
  refine hk.of_iso V.isoSpec.symm U.isoSpec.symm U.isoSpec.symm (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · exact Scheme.isoSpec_inv_naturality s
  · exact Scheme.isoSpec_inv_naturality t

/-- Every map invariant under the affine equivalence relation descends uniquely
to the quotient scheme, without assuming its target is affine. -/
theorem universal_property
    {U V S : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine S]
    (a : U ⟶ S) (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    (h : s ≫ a = t ≫ a) [IsClosedImmersion (pullback.lift s t h)]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := s.appTop.hom.toAlgebra; Module.Basis ι Γ(U, ⊤) Γ(V, ⊤))
    (T : Scheme.{u}) (f : U ⟶ T) (hf : s ≫ f = t ≫ f) :
    ∃! g : AffineRing.Construction.Affine.quotient s.appTop.hom t.appTop.hom ⟶ T, projection s t ≫ g = f := by
  obtain ⟨hfin, hflat, _, hsurj, hk⟩ := projection_properties a s t e h b
  let := hfin
  let := hflat
  let := hsurj
  exact Quotient.Construction.QuotientDescent.existsUnique_desc (projection s t) hk f hf

/-- For an affine equivalence relation with finite-free source over an affine
base, closedness of the relation follows from finiteness and joint monicity. -/
theorem projection_properties_of_finiteFree
    {U V S : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine S]
    (a : U ⟶ S) (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    (h : s ≫ a = t ≫ a)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := s.appTop.hom.toAlgebra; Module.Basis ι Γ(U, ⊤) Γ(V, ⊤)) :
    IsFinite (projection s t) ∧ Flat (projection s t) ∧
      LocallyOfFinitePresentation (projection s t) ∧ Surjective (projection s t) ∧
      IsKernelPair (projection s t) s t := by
  let := s.appTop.hom.toAlgebra
  have : IsFinite s := by
    have : IsFinite (Spec.map s.appTop) :=
      (IsFinite.SpecMap_iff s.appTop).mpr (Module.Finite.of_basis b)
    have heq : s = V.isoSpec.hom ≫ Spec.map s.appTop ≫ U.isoSpec.inv := by
      rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [heq]
    infer_instance
  have : JointlyMono₂ s t := e.toJointlyMono₂
  have : IsClosedImmersion (pullback.lift s t h) :=
    AffineSpanIs.Construction.AffineSpan.relation_isClosedImmersion a s t h
  exact projection_properties a s t e h b

/-- The finite basis may be supplied on the affine group scheme over the
base: the cartesian source square transports it to each affine object chart. -/
theorem projection_properties_of_source_baseChange
    {H U V S : Scheme.{u}} [IsAffine H] [IsAffine U] [IsAffine S]
    (hH : H ⟶ S) (a : U ⟶ S) (v : V ⟶ H) (s t : V ⟶ U)
    (hs : IsPullback v s hH a) (e : CategoryTheory.EquivalenceRelation s t)
    (h : s ≫ a = t ≫ a)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := hH.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤)) :
    IsFinite (projection s t) ∧ Flat (projection s t) ∧
      LocallyOfFinitePresentation (projection s t) ∧ Surjective (projection s t) ∧
      IsKernelPair (projection s t) s t := by
  let := hH.appTop.hom.toAlgebra
  have : IsFinite hH := by
    have : IsFinite (Spec.map hH.appTop) :=
      (IsFinite.SpecMap_iff hH.appTop).mpr (Module.Finite.of_basis b)
    have heq : hH = H.isoSpec.hom ≫ Spec.map hH.appTop ≫ S.isoSpec.inv := by
      rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [heq]
    infer_instance
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  have : IsAffine V := isAffine_of_isAffineHom s
  obtain ⟨bV, _⟩ := AffineGroupoidIs.Construction.AffineGroupoid.exists_basis_of_isPushout hH.appTop a.appTop
    v.appTop s.appTop (isPushout_appTop_of_isPullback hs) b
  exact projection_properties_of_finiteFree a s t e h bV

/-- The affine finite-free quotient theorem does not require a chosen base:
the canonical map to the spectrum of the integers supplies one. -/
theorem projection_properties_of_finiteFree_absolute
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := s.appTop.hom.toAlgebra; Module.Basis ι Γ(U, ⊤) Γ(V, ⊤)) :
    IsFinite (projection s t) ∧ Flat (projection s t) ∧
      LocallyOfFinitePresentation (projection s t) ∧ Surjective (projection s t) ∧
      IsKernelPair (projection s t) s t := by
  exact projection_properties_of_finiteFree (specULiftZIsTerminal.from U) s t e
    (specULiftZIsTerminal.hom_ext _ _) b

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineQuotientOf.Construction.AffineQuotient

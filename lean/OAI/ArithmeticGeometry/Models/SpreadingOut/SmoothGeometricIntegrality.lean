import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents
import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness

/-! # Smooth Geometric Integrality -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction

noncomputable section

/-! Connected smooth finite type schemes over a field are integral;
for smooth proper schemes geometric connectedness implies geometric irreducibility. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem smooth_connected_scheme_integral
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [Smooth f] [QuasiCompact f] [ConnectedSpace X] : IsIntegral X := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  let x : X := Classical.choice inferInstance
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let U := SmoothComponents.Construction.smoothComponentOpen f C
  have hcl : IsClopen (U : Set X) :=
    ⟨isClosed_of_mem_irreducibleComponents C.val C.property, U.isOpen⟩
  have hU : U = ⊤ := by
    apply SetLike.coe_injective
    exact hcl.eq_univ ⟨x, mem_irreducibleComponent⟩
  have hI : IsIntegral U.toScheme := SmoothComponents.Construction.smoothComponentOpen_integral f C
  rw [hU] at hI
  exact IsIntegral.of_isIso X.topIso.hom

theorem smooth_proper_geometricallyConnected_is_geometricallyIrreducible
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [Smooth f] [IsProper f] [GeometricallyConnected f] : GeometricallyIrreducible f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ g ↦ ?_⟩
  have : ConnectedSpace (pullback f g : Scheme.{u}) :=
    pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace L g
  have : IsIntegral (pullback f g : Scheme.{u}) := smooth_connected_scheme_integral (pullback.snd f g)
  infer_instance

theorem smooth_model_integral_of_integral_generic
    {R K : Type u} [CommRing R] [Field K] [IsReduced R]
    (φ : R →+* K) (hφ : Function.Injective φ)
    (X : Over (Spec (.of R))) [Smooth X.hom]
    [IsIntegral ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left] :
    IsIntegral X.left := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have : IsSchemeTheoreticallyDominant g := GenericFaithfulness.Construction.spec_injective_schematically_dominant φ hφ
  have : IsReduced X.left := GenericFaithfulness.Construction.smooth_model_reduced_of_injective_generic φ hφ X
  have : IsIntegral (pullback X.hom g : Scheme.{u}) := inferInstanceAs
    (IsIntegral ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left)
  have : IrreducibleSpace X.left := GeometricFieldComponents.Construction.irreducibleSpace_of_dominant (pullback.fst X.hom g)
  exact isIntegral_of_irreducibleSpace_of_isReduced X.left

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction

import OAI.ArithmeticGeometry.Models.SpreadingOut.TensorDomain
import OAI.ArithmeticGeometry.Models.SpreadingOut.Affine
import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenOver
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents
import OAI.ArithmeticGeometry.Models.FoundationsPullback
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Geometric Field Components -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents.Construction

noncomputable section

/-! Integral schemes over algebraically closed fields are geometrically
irreducible, hence geometrically connected. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

universe u

theorem affine_integral_baseChange_over_algClosed
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    (X : Over (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    IsIntegral ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj X).left := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let A := Γ(X.left, ⊤)
  let : Algebra k A := φ.hom.toAlgebra
  let e : X ≅ Affine.Construction.affineOver k A := Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫ Spec.map φ = X.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let i : F.obj X ≅ Affine.Construction.affineOver K (K ⊗[k] A) := F.mapIso e ≪≫ Affine.Construction.baseChangeAffineIso k K A
  have : IsDomain (K ⊗[k] A) := TensorDomain.Construction.tensor_domain_over_algClosed k K A
  have : IsIntegral (Affine.Construction.affineOver K (K ⊗[k] A)).left :=
    inferInstanceAs (IsIntegral (Spec (.of (K ⊗[k] A))))
  have : IsIso i.inv.left := inferInstanceAs (IsIso ((Over.forget _).map i.inv))
  exact IsIntegral.of_isIso i.inv.left

theorem pullback_square_range_fst
    {W X Y Z : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) : Set.range p = f ⁻¹' Set.range g := by
  have hs : Function.Surjective h.isoPullback.hom := h.isoPullback.hom.homeomorph.surjective
  rw [← h.isoPullback_hom_fst]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hs.range_eq, Set.image_univ, Scheme.Pullback.range_fst]

theorem irreducibleSpace_of_dominant
    {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Y) [IsDominant f] :
    IrreducibleSpace Y := by
  have hr := (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn
  rw [Set.image_univ] at hr
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set Y)
  rw [← f.denseRange.closure_range]
  exact hr.closure

theorem integral_baseChange_irreducible_over_algClosed
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    (X : Over (Spec (.of k))) [IsIntegral X.left] :
    IrreducibleSpace ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj X).left := by
  classical
  let x : X.left := Classical.choice inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : X.left.Opens := U
  let W := OpenOver.Construction.overOpen X V
  have : IsAffine W.left := hU
  have : Nonempty V.toScheme := ⟨⟨x, hxU⟩⟩
  have hVI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral W.left := hVI
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := Over.pullback g
  let i : (F.obj W).left ⟶ (F.obj X).left := (F.map (OpenOver.Construction.overOpenInclusion X V)).left
  have : IsIntegral (F.obj W).left := affine_integral_baseChange_over_algClosed k K W
  have hr : Set.range i = (pullback.fst X.hom g) ⁻¹' (V : Set X.left) := by
    have H := FoundationsPullback.Constructions.pullback_over_map_isPullback g (OpenOver.Construction.overOpenInclusion X V)
    simpa only [OpenOver.Construction.overOpenInclusion_range] using pullback_square_range_fst H
  have : IsDominant i := by
    rw [isDominant_iff, DenseRange, hr]
    exact (V.isOpen.dense ⟨x, hxU⟩).preimage (pullback.fst X.hom g).isOpenMap
  exact irreducibleSpace_of_dominant i

theorem integral_geometricallyIrreducible_over_algClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) : GeometricallyIrreducible f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ g ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  let : Algebra k K := φ.hom.toAlgebra
  have : IsIntegral (Over.mk f).left := inferInstanceAs (IsIntegral X)
  exact integral_baseChange_irreducible_over_algClosed k K (Over.mk f)

theorem integral_geometricallyConnected_over_algClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) : GeometricallyConnected f := by
  have := integral_geometricallyIrreducible_over_algClosed f
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ g ↦ ?_⟩
  have : IrreducibleSpace (pullback f g : Scheme.{u}) := inferInstance
  infer_instance

theorem smooth_proper_split_components_over_algClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) [Smooth X.hom] [IsProper X.hom] :
    Base.Construction.HasSplitGeometricComponents X := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := ⟨⟩
  let J := irreducibleComponents X.left
  have : Finite J := finite_irreducibleComponents_of_isNoetherian.to_subtype
  let : Fintype J := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let C := fun i ↦ SmoothComponents.Construction.smoothComponentOpen X.hom (e i)
  refine ⟨Fintype.card J, C, ?_, ?_, ?_⟩
  · intro i j hij
    exact SmoothComponents.Construction.smoothComponentOpen_disjoint X.hom (e i) (e j) (fun h ↦ hij (e.injective h))
  · change (⨆ i, SmoothComponents.Construction.smoothComponentOpen X.hom (e i)) = ⊤
    rw [e.iSup_comp, SmoothComponents.Construction.smoothComponentOpen_cover]
  · intro i
    have : IsIntegral (C i).toScheme := SmoothComponents.Construction.smoothComponentOpen_integral X.hom (e i)
    exact integral_geometricallyConnected_over_algClosed ((C i).ι ≫ X.hom)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents.Construction

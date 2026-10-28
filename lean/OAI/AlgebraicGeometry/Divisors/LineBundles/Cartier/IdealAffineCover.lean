import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealBundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularRingEquiv

/-! # Ideal Affine Cover -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealAffineCover.BundleCycles

noncomputable section

section

/-! Regular principal kernels on actual affine pullback charts prove
that the global image ideal is locally regular principal. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X) [QuasiCompact f]
    (C : X.OpenCover) (hAffine : ∀ i, IsAffine (C.X i))
    (W : C.I₀ → Scheme.{0}) (a : ∀ i, W i ⟶ Z) (b : ∀ i, W i ⟶ C.X i)
    (hp : ∀ i, IsPullback (b i) (a i) (C.f i) f)
    (t : ∀ i, Γ(C.X i, ⊤)) (ht : ∀ i, IsRegular (t i))
    (hk : ∀ i, RingHom.ker (b i).appTop.hom = Ideal.span {t i})

include hAffine hp ht hk in
theorem regularPrincipalImageIdeals_of_affineCover : IdealBundle.Cycles.HasRegularPrincipalImageIdeals f := by
  intro x
  obtain ⟨i, y, rfl⟩ := C.exists_eq x
  let : IsAffine (C.X i) := hAffine i
  let : QuasiCompact (b i) := MorphismProperty.of_isPullback (hp i).flip inferInstance
  let U : X.affineOpens := ⟨C.f i ''ᵁ (⊤ : (C.X i).Opens), (isAffineOpen_top (C.X i)).image_of_isOpenImmersion _⟩
  let e : Γ(X, U.1) ≅ Γ(C.X i, ⊤) := (C.f i).appIso ⊤
  refine ⟨U, ⟨y, trivial, rfl⟩, e.inv (t i), RegularRingEquiv.BundleCycles.regular_ringEquiv e.commRingCatIsoToRingEquiv.symm (t i) (ht i), ?_⟩
  have hbase := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f (b i) (a i) (C.f i) (hp i)
    (⟨⊤, isAffineOpen_top (C.X i)⟩ : (C.X i).affineOpens)
  have hc : RingHom.ker (b i).appTop.hom = (RingHom.ker (f.app U.1).hom).comap e.inv.hom :=
    (Scheme.Hom.ker_apply (b i) ⟨⊤, isAffineOpen_top (C.X i)⟩).symm.trans
      (hbase.trans (congrArg (Ideal.comap e.inv.hom) (Scheme.Hom.ker_apply f U)))
  have hmap := congrArg (Ideal.map e.inv.hom) (hc.symm.trans (hk i))
  exact (Ideal.map_comap_of_surjective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).2
    (RingHom.ker (f.app U.1).hom)).symm.trans
      (hmap.trans (by rw [Ideal.map_span, Set.image_singleton]))

end

/-! Regular principal image ideals descend from an actual open cover
with cartesian charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X) [QuasiCompact f]
    (C : X.OpenCover) (W : C.I₀ → Scheme.{0}) (a : ∀ i, W i ⟶ Z) (b : ∀ i, W i ⟶ C.X i)
    (hp : ∀ i, IsPullback (b i) (a i) (C.f i) f)
    (hloc : ∀ i, IdealBundle.Cycles.HasRegularPrincipalImageIdeals (b i))

include hp hloc in
theorem regularPrincipalImageIdeals_of_openCover : IdealBundle.Cycles.HasRegularPrincipalImageIdeals f := by
  intro x
  obtain ⟨i, y, rfl⟩ := C.exists_eq x
  obtain ⟨U, hyU, t, ht, hker⟩ := hloc i y
  let : QuasiCompact (b i) := MorphismProperty.of_isPullback (hp i).flip inferInstance
  let V : X.affineOpens := ⟨C.f i ''ᵁ U.1, U.2.image_of_isOpenImmersion _⟩
  let e : Γ(X, V.1) ≅ Γ(C.X i, U.1) := (C.f i).appIso U.1
  refine ⟨V, ⟨y, hyU, rfl⟩, e.inv t, RegularRingEquiv.BundleCycles.regular_ringEquiv e.commRingCatIsoToRingEquiv.symm t ht, ?_⟩
  have hbase := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f (b i) (a i) (C.f i) (hp i) U
  have hc : RingHom.ker ((b i).app U.1).hom = (RingHom.ker (f.app V.1).hom).comap e.inv.hom :=
    (Scheme.Hom.ker_apply (b i) U).symm.trans
      (hbase.trans (congrArg (Ideal.comap e.inv.hom) (Scheme.Hom.ker_apply f V)))
  have hmap := congrArg (Ideal.map e.inv.hom) (hc.symm.trans hker)
  exact (Ideal.map_comap_of_surjective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).2
    (RingHom.ker (f.app V.1).hom)).symm.trans
      (hmap.trans (by rw [Ideal.map_span, Set.image_singleton]))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealAffineCover.BundleCycles

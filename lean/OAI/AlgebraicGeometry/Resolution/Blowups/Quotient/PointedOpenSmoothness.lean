import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.LocalSmoothness

/-! # Pointed Open Smoothness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.PointedOpenSmoothness.Construction

noncomputable section

/-! Smoothness of a quotient can be checked only at points on its actual closed center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_quotient_of_pointed_open_charts
    (k : Type u) [CommRing k] {R : Type u} [CommRing R] [Algebra k R] (I : Ideal R)
    (hlocal : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (φ : R →ₐ[k] S),
        IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) ∧
        ∃ q : PrimeSpectrum S, PrimeSpectrum.comap φ.toRingHom q = p ∧
          Algebra.Smooth k (S ⧸ I.map φ.toRingHom)) :
    Algebra.Smooth k (R ⧸ I) := by
  let Q := R ⧸ I
  let pR (p : PrimeSpectrum Q) := PrimeSpectrum.comap (Ideal.Quotient.mk I) p
  have hI (p : PrimeSpectrum Q) : I ≤ (pR p).asIdeal := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p.asIdeal.zero_mem
  choose S alg φ hopen q hq hs using fun p : PrimeSpectrum Q => hlocal (pR p) (hI p)
  let : ∀ p, Algebra k (S p) := alg
  let : ∀ p, Algebra R (S p) := fun p => (φ p).toRingHom.toAlgebra
  let : ∀ p, IsScalarTower k R (S p) := fun p =>
    IsScalarTower.of_algebraMap_eq (fun x => ((φ p).commutes x).symm)
  let T (p : PrimeSpectrum Q) := S p ⧸ I.map (algebraMap R (S p))
  let : ∀ p, IsScalarTower k Q (T p) := fun _ => Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I
  let c := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let f := Spec.map (CommRingCat.ofHom (algebraMap k Q))
  let r (p : PrimeSpectrum Q) := Spec.map (CommRingCat.ofHom (algebraMap R (S p)))
  let j (p : PrimeSpectrum Q) := Spec.map (CommRingCat.ofHom (algebraMap Q (T p)))
  let g (p : PrimeSpectrum Q) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R (S p)))))
  let : ∀ p, IsOpenImmersion (r p) := hopen
  have hpb (p : PrimeSpectrum Q) : IsPullback (j p) (g p) c (r p) :=
    Affine.QuotientBaseChange.Construction.affineQuotient_baseChange_isPullback (S := S p) I
  let : ∀ p, IsOpenImmersion (j p) := fun p =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb p).flip inferInstance
  have hcover : ⨆ p, (j p).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro p _
    change PrimeSpectrum Q at p
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨p, ?_⟩
    rw [SupportedBlowupSmoothGluing.Construction.opensRange_of_open_pullback (j p) (g p) c (r p) (hpb p)]
    exact ⟨q p, hq p⟩
  have hlocal' (p : PrimeSpectrum Q) : Smooth (j p ≫ f) := by
    have ht : Algebra.Smooth k (T p) := hs p
    rw [← Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap k Q) ≫ CommRingCat.ofHom (algebraMap Q (T p)) =
        CommRingCat.ofHom (algebraMap k (T p)) := by
      ext x
      exact (IsScalarTower.algebraMap_apply k Q (T p) x).symm
    rw [he]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr ht)
  have hf : Smooth f := by
    let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun p => (j p).opensRange) hcover
    intro p
    let : Smooth (j p ≫ f) := hlocal' p
    exact SupportedBlowupSmoothGluing.Construction.smooth_on_opensRange_of_open_immersion f (j p)
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hf)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.PointedOpenSmoothness.Construction

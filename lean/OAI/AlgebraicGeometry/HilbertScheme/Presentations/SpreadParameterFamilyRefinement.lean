import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationFamilyEqualityNeighborhood
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.RefinementPoint

/-! # Spread Parameter Family Refinement -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpreadParameterFamilyRefinement.GradedHilbert

noncomputable section

/-! A parameter extending a correct local Hilbert parameter becomes a
correct family parameter after shrinking its principal neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {A : Type u} [CommRing A] {n : ℕ}

theorem refine_spread_family_parameter
    (a : Spec (.of A) ⟶ S) (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (H : Over S) (U : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) H)
    (p : PrimeSpectrum A)
    (xp : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal))) ≫ a) ⟶ H)
    (hxp : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) xp U =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
        (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap A (Localization.AtPrime p.asIdeal))) F)
    (s : A) (hs : s ∉ p.asIdeal)
    (xs : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ a) ⟶ H)
    (hxs : Spec.map (CommRingCat.ofHom (Principal.PrimeLocalization.principalToPrimeMap p.asIdeal s hs)) ≫ xs.left = xp.left) :
    ∃ (V : Over S) (b : V ⟶ Over.mk a), IsOpenImmersion b.left ∧ p ∈ Set.range b.left ∧
      ∃ x : V ⟶ H, Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x U =
        Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F := by
  let As := Localization.Away s
  let Ap := Localization.AtPrime p.asIdeal
  let aspec : Spec (.of As) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap A As)) ≫ a
  let ap : Spec (.of Ap) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap A Ap)) ≫ a
  let bs := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap A As)
  let bp := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap A Ap)
  let q := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap aspec (Principal.PrimeLocalization.principalToPrimeMap p.asIdeal s hs)
  have hbase : Spec.map (CommRingCat.ofHom (Principal.PrimeLocalization.principalToPrimeMap p.asIdeal s hs)) ≫ aspec = ap := by
    change _ ≫ (_ ≫ a) = _ ≫ a
    rw [← Category.assoc, Principal.RefinementPoint.principalToPrime_spec_comp]
  let e : Over.mk (Spec.map (CommRingCat.ofHom (Principal.PrimeLocalization.principalToPrimeMap p.asIdeal s hs)) ≫ aspec) ⟶ Over.mk ap :=
    Over.homMk (𝟙 (Spec (.of Ap))) ((Category.id_comp _).trans hbase.symm)
  have hb : q ≫ bs = e ≫ bp := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Principal.PrimeLocalization.principalToPrimeMap p.asIdeal s hs)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A As)) = (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ap))
    rw [Category.id_comp]
    exact Principal.RefinementPoint.principalToPrime_spec_comp p.asIdeal s hs
  have hx : q ≫ xs = e ≫ xp := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Principal.PrimeLocalization.principalToPrimeMap p.asIdeal s hs)) ≫ xs.left = (𝟙 _) ≫ xp.left
    rw [Category.id_comp]
    exact hxs
  let Fs := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) bs F
  let Gs := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) xs U
  have hfg : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) q Fs =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) q Gs := by
    dsimp only [Fs, Gs]
    rw [← Hilbert.Functor.pullbackFamily_comp, ← Hilbert.Functor.pullbackFamily_comp, hb, hx,
      Hilbert.Functor.pullbackFamily_comp, Hilbert.Functor.pullbackFamily_comp, hxp]
  let : Algebra As Ap := (Principal.PrimeLocalization.principalToPrimeMap p.asIdeal s hs).toAlgebra
  let W := p.asIdeal.primeCompl.map (algebraMap A As)
  let : IsLocalization W Ap := Principal.PrimeLocalizationTower.principalToPrime_isLocalization p.asIdeal s hs
  obtain ⟨t, ht⟩ := LocalizationFamilyEqualityNeighborhood.GradedHilbert.nativeFamily_equality_localization_neighborhood aspec Fs Gs W Ap hfg
  let δ := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap aspec (algebraMap As (Localization.Away t.val))
  refine ⟨_, δ ≫ bs, ?_, ?_, δ ≫ xs, ?_⟩
  · exact inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap As (Localization.Away t.val))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A As))))
  · obtain ⟨y, hy⟩ := Principal.RefinementPoint.principalRefinement_contains_prime p s hs t
    exact ⟨y, hy⟩
  · rw [Hilbert.Functor.pullbackFamily_comp, Hilbert.Functor.pullbackFamily_comp]
    exact ht.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpreadParameterFamilyRefinement.GradedHilbert

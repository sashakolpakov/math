import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedOpenRestrictionScalar

/-! # Supported Candidate -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCandidate

noncomputable section

/-! A class fixed by the selected source function is the genuine
section-supported extension of its restriction to D(z). The equality
holds in the original ambient principal cohomology before forgetting
support or mapping to de Rham cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem transport_section {D : Type*} [Category D] {A B C E : D}
    (e : A ≅ C) (f : B ≅ E) (s : E ⟶ C) (r : A ⟶ B) (t : C ⟶ E)
    (hs : s ≫ t = 𝟙 E) (hr : r ≫ f.hom = e.hom ≫ t) :
    (f.hom ≫ s ≫ e.inv) ≫ r = 𝟙 B := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Category.id_comp]
  rw [hr, Iso.inv_hom_id_assoc, hs, Category.comp_id]

private theorem after_candidate {A B C : AddCommGrpCat}
    (s : B ⟶ A) (f : A ⟶ C) (g : B ⟶ C) (h : s ≫ f = g)
    (x : A) (y : B) (hx : x = s y) : f x = g y := by
  rw [hx]
  exact ConcreteCategory.congr_hom h y

open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
variable {Y X Z : Scheme.{0}} [Y.IsSeparated] (f : Y ⟶ X) (i : X ⟶ Z)
  [IsAffineHom (f ≫ i)] (U : Z.Opens) (hU : IsAffineOpen U)
  {g : ℕ} (t : Fin g → Γ(Z,U)) (N : Y.Modules) [N.IsQuasicoherent]
  (z : Γ(Y,(f ≫ i) ⁻¹ᵁ U)) (O₁ O₂ : Y.Opens)
  (H : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (OpenReindex.wideOpens (f ≫ i) U hU) (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
    (PrincipalPoint.Fraction.family U t) O₁ O₂)

private abbrev family := PrincipalPoint.Fraction.family U t
private abbrev group (c q : ℕ) := (OpenRestriction.supportedFunctor U (family U t) c q).obj
  (OpenFixedClass.source f i U hU N)
private abbrev forgetScalars : ModuleCat.{0} Γ(Z,U) ⥤ AddCommGrpCat := forget₂ _ _

include hU in
private theorem ambient_open_affine : IsAffineHom (((f ≫ i) ⁻¹ᵁ U).ι) where
  isAffine_preimage V hV := by
    apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (((f ≫ i) ⁻¹ᵁ U).ι)).mp
    simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] using
      (hU.preimage (f ≫ i)).inf hV

include hU in
private theorem extension_qc : (OpenRestriction.extension ((f ≫ i) ⁻¹ᵁ U) N).IsQuasicoherent := by
  let := ambient_open_affine f i U hU
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (((f ≫ i) ⁻¹ᵁ U).ι)

def candidate (c q : ℕ) :
    (forgetScalars U).obj (group f i U hU t (OpenRestriction.extension (Y.basicOpen z) N) c q) ⟶
      (forgetScalars U).obj (group f i U hU t N c q) :=
  (SupportedCoordinates.localIso f i U hU (family U t) N c q (Y.basicOpen z)).hom ≫
    H.candidate N c q ≫
      (SupportedCoordinates.wideIso f i U hU (family U t) N c q).inv

def forgetSupport (c q : ℕ) :=
  (SupportedCoordinates.wideIso f i U hU (family U t) N c q).hom ≫
    H.forgetSupport N c q

def selectedExtension (c q : ℕ) :=
  (SupportedCoordinates.localIso f i U hU (family U t) N c q (Y.basicOpen z)).hom ≫
    H.selectedExtension N c q

omit [Y.IsSeparated] [IsAffineHom (f ≫ i)] in
theorem candidate_restriction (c q : ℕ) :
    SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c q ≫
      (forgetScalars U).map (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c q) = 𝟙 _ := by
  let eW := SupportedCoordinates.wideIso f i U hU (family U t) N c q
  let eL := SupportedCoordinates.localIso f i U hU (family U t) N c q (Y.basicOpen z)
  have hr := SupportedCoordinates.restriction_square
    f i U hU (family U t) N c q (Y.basicOpen z)
  have hs := H.candidate_restriction N c (OpenReindex.geometricInclusion (f ≫ i) U hU (Y.basicOpen z)) q
  exact transport_section eW eL (H.candidate N c q) _ _ hs hr

omit [Y.IsSeparated] [IsAffineHom (f ≫ i)] in
theorem candidate_global (c q : ℕ) :
    SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c q ≫ SupportedCandidate.forgetSupport f i U hU t N z O₁ O₂ H c q =
      SupportedCandidate.selectedExtension f i U hU t N z O₁ O₂ H c q := by
  dsimp only [SupportedCandidate.candidate, SupportedCandidate.forgetSupport, SupportedCandidate.selectedExtension]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [H.candidate_global]

private theorem candidate_restriction_fixed (c q : ℕ) (x : group f i U hU t N c q)
    (hx : (OpenRestriction.supportedFunctor U (family U t) c q).map
      (OpenFixedClass.scalar f i U hU N z) x = x) :
    (OpenRestriction.supportedFunctor U (family U t) c q).map
        (OpenFixedClass.scalar f i U hU N z)
        (SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c q
          (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c q x)) =
      SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c q
        (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c q x) := by
  let := extension_qc f i U hU N
  let eW := SupportedCoordinates.wideIso f i U hU (family U t) N c q
  let eL := SupportedCoordinates.localIso f i U hU (family U t) N c q (Y.basicOpen z)
  have hx' := (SupportedCoordinates.scalar_fixed_iff
    f i U hU (family U t) N c q z x).mpr hx
  have hy := Principal.SupportedOpenRestrictionScalar.fixed_restriction
    (OpenReindex.wideOpens (f ≫ i) U hU) (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
    (OpenReindex.geometricInclusion (f ≫ i) U hU (Y.basicOpen z)) (family U t) ((f ≫ i) ⁻¹ᵁ U)
    (SupportConditions.wide_bounded (f ≫ i) U hU)
    (SupportConditions.local_bounded (f ≫ i) U hU (Y.basicOpen z))
    N c q z (eW.hom x) hx'
  have hr := ConcreteCategory.congr_hom
    (SupportedCoordinates.restriction_square
      f i U hU (family U t) N c q (Y.basicOpen z)) x
  change eL.hom (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c q x) =
    Principal.SupportedOpenRestrictionScalar.restriction
      (OpenReindex.wideOpens (f ≫ i) U hU) (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
      (OpenReindex.geometricInclusion (f ≫ i) U hU (Y.basicOpen z)) (family U t) N c q (eW.hom x) at hr
  rw [← hr] at hy
  have hc := Principal.SupportedOpenScalar.candidate_fixed
    (OpenReindex.wideOpens (f ≫ i) U hU) ((f ≫ i) ⁻¹ᵁ U)
    (SupportConditions.wide_bounded (f ≫ i) U hU) (family U t) N c
    (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
    (SupportConditions.local_bounded (f ≫ i) U hU (Y.basicOpen z)) O₁ O₂ H z q
    (eL.hom (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c q x)) hy
  apply (SupportedCoordinates.scalar_fixed_iff
    f i U hU (family U t) N c q z _).mp
  change Principal.SupportedOpenScalar.action (OpenReindex.wideOpens (f ≫ i) U hU) ((f ≫ i) ⁻¹ᵁ U)
      (SupportConditions.wide_bounded (f ≫ i) U hU) (family U t) N c z q
      (eW.hom (eW.inv _)) = eW.hom (eW.inv _)
  simp only [Iso.inv_hom_id_apply]
  convert hc using 1

theorem recovery (c n : ℕ) (x : group f i U hU t N c (n+c))
    (hx : (OpenRestriction.supportedFunctor U (family U t) c (n+c)).map
      (OpenFixedClass.scalar f i U hU N z) x = x) :
    x = SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c (n+c)
      (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c) x) := by
  apply OpenFixedClass.eq_of_map_eq f i U hU N z (family U t) c n x _ hx
    (candidate_restriction_fixed f i U hU t N z O₁ O₂ H c (n+c) x hx)
  exact (ConcreteCategory.congr_hom (SupportedCandidate.candidate_restriction f i U hU t N z O₁ O₂ H c (n+c))
    (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c) x)).symm

theorem global_recovery (c n : ℕ) (x : group f i U hU t N c (n+c))
    (hx : (OpenRestriction.supportedFunctor U (family U t) c (n+c)).map
      (OpenFixedClass.scalar f i U hU N z) x = x) :
    SupportedCandidate.forgetSupport f i U hU t N z O₁ O₂ H c (n+c) x =
      SupportedCandidate.selectedExtension f i U hU t N z O₁ O₂ H c (n+c)
        (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c) x) :=
  after_candidate (SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c (n+c))
    (SupportedCandidate.forgetSupport f i U hU t N z O₁ O₂ H c (n+c))
    (SupportedCandidate.selectedExtension f i U hU t N z O₁ O₂ H c (n+c))
    (SupportedCandidate.candidate_global f i U hU t N z O₁ O₂ H c (n+c)) x
    (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c) x)
    (recovery f i U hU t N z O₁ O₂ H c n x hx)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCandidate

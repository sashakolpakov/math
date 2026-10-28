import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineSectionCoordinates

/-! # Affine Cech -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCech.Construction

noncomputable section

/-! Vanishing of additive degree-one Čech cocycles for affine quasicoherent sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

variable (R : CommRingCat.{u})
    (F : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (PrimeSpectrum R)))
    (hF : ∀ r : R, IsLocalizedModule (Submonoid.powers r)
      (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom)
    {ι : Type v} [Fintype ι] [DecidableEq ι] (f : ι → R)

abbrev affineCechC0 := ∀ i, F.obj.obj (op (PrimeSpectrum.basicOpen (f i)))
abbrev affineCechC1 := ∀ i j, F.obj.obj (op (PrimeSpectrum.basicOpen (f i * f j)))
abbrev affineCechC2 := ∀ i j k, F.obj.obj (op (PrimeSpectrum.basicOpen (f i * (f j * f k))))

def affineCechD0 : affineCechC0 R F f →ₗ[R] affineCechC1 R F f :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f j) (f i * f j) (dvd_mul_left _ _) ∘ₗ LinearMap.proj j -
      AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f i) (f i * f j) (dvd_mul_right _ _) ∘ₗ LinearMap.proj i

def affineCechD1 : affineCechC1 R F f →ₗ[R] affineCechC2 R F f :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f j * f k) (f i * (f j * f k)) (dvd_mul_left _ _) ∘ₗ
        LinearMap.proj k ∘ₗ LinearMap.proj j -
      AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f i * f k) (f i * (f j * f k))
        (by use f j; ring) ∘ₗ LinearMap.proj k ∘ₗ LinearMap.proj i +
      AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f i * f j) (f i * (f j * f k))
        (by use f k; ring) ∘ₗ LinearMap.proj j ∘ₗ LinearMap.proj i

def affineCechEquiv0 : PrincipalCech.Construction.principalCechC0 R f (F.obj.obj (op ⊤)) ≃ₗ[R] affineCechC0 R F f :=
  LinearEquiv.piCongrRight fun i ↦ AffineSectionCoordinates.Construction.affineBasicSectionEquiv R F hF (f i)

def affineCechEquiv1 : PrincipalCech.Construction.principalCechC1 R f (F.obj.obj (op ⊤)) ≃ₗ[R] affineCechC1 R F f :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦
    AffineSectionCoordinates.Construction.affineBasicSectionEquiv R F hF (f i * f j)

def affineCechEquiv2 : PrincipalCech.Construction.principalCechC2 R f (F.obj.obj (op ⊤)) ≃ₗ[R] affineCechC2 R F f :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦
    LinearEquiv.piCongrRight fun k ↦ AffineSectionCoordinates.Construction.affineBasicSectionEquiv R F hF (f i * (f j * f k))

omit [Fintype ι] [DecidableEq ι] in
theorem affineCechD0_comparison (x : PrincipalCech.Construction.principalCechC0 R f (F.obj.obj (op ⊤))) :
    affineCechD0 R F f (affineCechEquiv0 R F hF f x) =
      affineCechEquiv1 R F hF f (PrincipalCech.Construction.principalCechD0 R f (F.obj.obj (op ⊤)) x) := by
  funext i j
  simp [affineCechD0, affineCechEquiv0, affineCechEquiv1, PrincipalCech.Construction.principalCechD0,
    AffineSectionCoordinates.Construction.affineBasicSectionEquiv_restrict_apply R F hF]

omit [Fintype ι] [DecidableEq ι] in
theorem affineCechD1_comparison (z : PrincipalCech.Construction.principalCechC1 R f (F.obj.obj (op ⊤))) :
    affineCechD1 R F f (affineCechEquiv1 R F hF f z) =
      affineCechEquiv2 R F hF f (PrincipalCech.Construction.principalCechD1 R f (F.obj.obj (op ⊤)) z) := by
  funext i j k
  simp [affineCechD1, affineCechEquiv1, affineCechEquiv2, PrincipalCech.Construction.principalCechD1,
    AffineSectionCoordinates.Construction.affineBasicSectionEquiv_restrict_apply R F hF]

include hF in
theorem affineCech_exact_degreeOne (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Exact (affineCechD0 R F f) (affineCechD1 R F f) := by
  intro z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := (affineCechEquiv1 R F hF f).surjective z
    rw [affineCechD1_comparison] at hz
    have hw : PrincipalCech.Construction.principalCechD1 R f (F.obj.obj (op ⊤)) w = 0 :=
      (affineCechEquiv2 R F hF f).injective (hz.trans (map_zero _).symm)
    obtain ⟨x, hx⟩ := (PrincipalCech.Construction.principalCech_exact_degreeOne R f (F.obj.obj (op ⊤)) hf w).mp hw
    refine ⟨affineCechEquiv0 R F hF f x, ?_⟩
    rw [affineCechD0_comparison, hx]
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (affineCechEquiv0 R F hF f).surjective x
    rw [affineCechD0_comparison, affineCechD1_comparison]
    have h := LinearMap.congr_fun (PrincipalCech.Construction.principalCechD1_comp_D0 R f (F.obj.obj (op ⊤))) y
    change PrincipalCech.Construction.principalCechD1 R f (F.obj.obj (op ⊤))
      (PrincipalCech.Construction.principalCechD0 R f (F.obj.obj (op ⊤)) y) = 0 at h
    rw [h, map_zero]

theorem quasicoherent_affineCech_exact (N : (Spec R).Modules) [N.IsQuasicoherent]
    (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Exact (affineCechD0 R (modulesSpecToSheaf.obj N) f)
      (affineCechD1 R (modulesSpecToSheaf.obj N) f) := by
  have hN : IsLocalizing (modulesSpecToSheaf.obj N) :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance
  exact affineCech_exact_degreeOne R (modulesSpecToSheaf.obj N) hN f hf

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCech.Construction
